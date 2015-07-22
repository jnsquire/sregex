#!/usr/bin/env perl

# Copyright (C) 2015 Yichun Zhang (agentzh)

use 5.010001;
use strict;
use warnings;

use IPC::Run3 qw( run3 );
use Data::Dumper qw( Dumper );
use GraphViz ();
#use Time::HiRes qw( time );
use List::MoreUtils qw( uniq firstidx );
use List::Util qw( first max );
use Carp qw( croak carp );
use Getopt::Long qw( GetOptions );
use File::Temp qw( tempfile );
use POSIX qw( tmpnam );
use File::Spec ();
use FindBin ();

sub add_nfa_edges ($$$$);
sub gen_nfa_edge_label ($);
sub escape_char ($);
sub escape_range_char ($);
sub gen_nfa ();
sub draw_nfa ($);
sub is_node ($);
sub opcode ($);
sub gen_dfa_edges ($$$$$$);
sub gen_dfa ($);
sub dedup_nfa_edges ($);
sub reorder_nfa_edges ($$);
sub draw_dfa ($);
sub escape_range ($$);
sub gen_dfa_hash_key ($$);
sub add_to_set ($$);
sub remove_from_set ($$);
sub gen_dfa_node_label ($);
sub gen_dfa_edge_label ($$);
sub gen_c_from_dfa ($);
sub canon_range ($);
sub usage ($);
sub gen_dfa_edge ($$$$$);
sub resolve_dfa_edge ($$$$$$$$);
sub gen_dfa_edges_for_asserts ($$$$$$);
sub gen_capture_handler_c_code ($$$$);
sub gen_c_from_dfa_edge ($$$$$);
sub gen_c_from_dfa_node ($$);
sub dump_code ($);
sub count_chars_in_ranges ($);
sub analyze_dfa ($);

my $cc = "cc";
my $debug = 0;

GetOptions("help|h",        \(my $help),
           "cc=s",          \$cc,
           "repeat=i",      \(my $repeat),
           "debug=i",       \$debug,
           "g",             \(my $global),
           "out|o=s",       \(my $exefile),
           "timer",         \(my $timer),
           "stdin",         \(my $stdin))
   or die usage(1);

if ($help) {
    usage(0);
}

if (!$timer) {
    if (defined $repeat) {
        warn "WARNING: --repeat is ignored because --timer is not specified.\n";
    }
    $repeat = 1;
    $timer = 0;

} elsif (!$repeat) {
    $repeat = 5;
}

$Data::Dumper::Terse = 1;

my $re = shift;
if (!defined $re) {
    warn "No regex specified.\n";
    usage(1);
}

my $subject;
if ($stdin) {
    my $first = <STDIN>;
    if ($first =~ s/^(\d+)$//s) {
        my $len = $1;
        if (!defined read(STDIN, $subject, $len)) {
            die "failed to read stdin: $!\n";
        }

    } else {
        die "the stdin output must come with a length prefix line but got: $first\n";
    }

} else {
    $subject = shift;
    if (!defined $subject) {
        warn "No subject nor --stdin specified.\n";
        usage(1);
    }
}

#die "subject: $subject";

my @opts;
# a hack to work-around the lack of support of (?i) in the sregex frontend.
if ($re =~ s/^\(\?i\)//) {
    push @opts, "--flags", "i";
}
my @cmd = ("$FindBin::Bin/sregex-cli", @opts, $re);
run3 \@cmd, undef, \(my $res), \(my $err);

if (!$res) {
    if ($err) {
        warn $err;
    }
    die "sregex-cli crashed.\n";
}

warn "$res" if $debug;
open my $in, "<", \$res or die $!;

my (@bytecodes, $found);
while (<$in>) {
    if (!$found) {
        if (/^ 0\. split/) {
            $found = 1;

        } else {
            next;
        }
    }

    if (/^ \s* (\d+) \. \s (\w+) (?:\s (.+))?/x) {
        my ($idx, $opcode, $args) = ($1, $2, $3);
        if ($idx != @bytecodes) {
            die "Bad bytecode index: $1: $_";
        }

        if (defined $args) {
            my @args = split /\s*,\s+/, $args;
            if ($opcode =~ /^(?:not)?in$/) {
                @args = map { split /-/, $_ } @args;
            }
            push @bytecodes, [$opcode, @args];

        } else {
            push @bytecodes, $opcode;
        }

    } else {
        die "Bad bytecode: $_";
    }
}

close $in;

#warn Dumper \@bytecodes;

my $big;
my %cached_labels;
my %escaped_range_chars = (
    "\t" => '\t',
    "\n" => '\n',
    "\r" => '\r',
    " " => '\ ',
    "\e" => '\e',
    "\f" => '\f',
    "\\" => "\\\\",
    "^" => "\\^",
    '$' => "\\\$",
    '(' => "\\(",
    ')' => "\\)",
    '[' => "\\[",
    ']' => "\\]",
    '-' => "\\-",
);

my %escaped_chars = (
    "\t" => '\t',
    "\n" => '\n',
    " " => '\ ',
    "\e" => '\e',
    "\f" => '\f',
    "\\" => "\\\\",
);

my @edge_colors = qw(
    red
    darkgreen
    blue
    purple
    black
);

my $node_attr =
{
    shape => 'circle',
    style => 'filled',
    fillcolor => 'yellow',
};
$node_attr->{height} = 0.1 if $big;

my $edge_attr =
{
    color => 'red',
};
if ($big) {
    $edge_attr->{arrowsize} = 0.5;
} else {
    #$edge_attr->{len} = 1.4;
}

my %nfa_paths;
my %pc2assert;
my $used_asserts;

#my $begin = time;
my $nfa = gen_nfa();
#my $elapsed = time - $begin;
#warn "NFA generated ($elapsed sec).\n";
#warn Dumper($nfa);
draw_nfa($nfa) if $debug;

#$begin = time;
my $dfa = gen_dfa($nfa);
#$elapsed = time - $begin;
#warn "DFA generated ($elapsed sec).\n";
analyze_dfa($dfa);

#warn Dumper($dfa);
draw_dfa($dfa) if $debug;

#exit;
my $c = gen_c_from_dfa($dfa);
warn dump_code($c) if $debug == 2;
#$begin = time;
{
    my ($fh, $fname) = tempfile(SUFFIX => '.c', UNLINK => 1);
    #warn $fname;
    print $fh $c;
    close $fh;

    my $exe_tmp;
    if (!defined $exefile) {
        $exefile = tmpnam();
        $exe_tmp = 1;
    } else {
        unlink $exefile if -f $exefile;
    }

    #system("cc -o $exefile -Wall -Wno-unused-label -Wno-unused-variable -Wno-unused-but-set-variable -Werror -O0 $fname") == 0
    my $extra_ccopt = "";
    if ($debug && $cc =~ /\bgcc\b/) {
        $extra_ccopt = "-Wall -Wno-unused-label -Wno-unused-variable -Wno-unused-but-set-variable -Werror";
    }

    my $cmd = "$cc -o $exefile $extra_ccopt $fname";
    #warn $cmd;
    system($cmd) == 0 or die "$!\n";

    #{
        #my @info = stat $exefile;
        #my $size = $info[7];
        #if ($size >= 1024 * 1024) {
            #warn "$re - size $size\n";
        #}
    #}

    my $path = File::Spec->rel2abs($exefile);
    my @cmd = ($path);

    #my $begin = time;
    #$elapsed = time - $begin;
    #warn "Perl code execution done ($elapsed sec).\n";

    run3 \@cmd, \$subject, \(my $out), \(my $err);

    my $rc = $?;

    if ($err) {
        print STDERR $err;
    }

    if ($rc != 0) {
        die "failed to run the executable file $exefile: $rc\n";
    }

    if ($exe_tmp) {
        unlink $exefile or die $!;
    } else {
        #warn "file $exefile generated.\n";
    }

    if (!defined $out) {
        die "program crashed: $rc";
    }

    print $out;
}

sub gen_nfa () {
    my @nodes;
    my $max_cap = 0;
    my $idx = 0;
    for my $bc (@bytecodes) {
        my $opcode = opcode($bc);
        if ($opcode eq 'assert') {
            $used_asserts = 1;
            if (!exists $pc2assert{$idx}) {
                #warn "new assert $bc->[1]";
                $pc2assert{$idx} = $bc->[1];
                $found = 1;
            }
        } elsif ($opcode eq 'save') {
            my $n = $bc->[1];
            if ($n > $max_cap) {
                $max_cap = $n;
            }
        }

        $opcode = is_node($bc);
        if (defined $opcode || $idx == 0) {
            my $node = {
                idx => $idx,
                edges => [],
                $idx == 0 ? (start => 1) : (),
            };
            if (defined $opcode) {
                #warn $opcode;
                if ($opcode eq 'match') {
                    $node->{accept} = 1;
                } elsif ($opcode eq 'in' or $opcode eq 'notin') {
                    #warn "HERE";
                    my @args = @$bc;
                    shift @args;
                    #warn "pre: @args";
                    canon_range(\@args);
                    #warn "post: @args";
                    @$bc = ($opcode, @args);
                }
            }
            push @nodes, $node;
        }
        $idx++;
    }

    for my $node (@nodes) {
        my %visited;
        my $idx = $node->{idx};
        add_nfa_edges($node, $idx == 0 ? 0 : $idx + 1, \%visited, undef);
    }

    return {
        nodes => \@nodes,
        nvec => $max_cap + 1,
    }
}

sub draw_nfa ($) {
    my ($nfa) = @_;

    my $graph = GraphViz->new(
        layout => $big ? 'twopi' : 'neato',
        ratio => 'auto',
        node => $node_attr,
        edge => $edge_attr,
    );

    my $nfa_nodes = $nfa->{nodes};

    #$graph->as_dot("nfa.dot");
    for my $node (@$nfa_nodes) {
        my $idx = $node->{idx};
        $graph->add_node("n$idx", $node->{start} ? (color => 'orange') : (),
                         $node->{accept} ? (shape => 'doublecircle') : (),
                         label => $big ? '' : $idx || " $idx");
    }
    for my $node (@$nfa_nodes) {
        my $from_idx = $node->{idx};
        my $e_idx = 0;
        for my $e (@{ $node->{edges} }) {
            my $label = gen_nfa_edge_label($e);
            my $to_idx = $e->[-1];
            my $color = $edge_colors[$e_idx] || 'black';
            $graph->add_edge("n$from_idx" => "n$to_idx", label => $label, color => $color, len => 1.6);
            $e_idx++;
        }
    }
    $graph->as_png("nfa.png");
}

sub add_nfa_edges ($$$$) {
    my ($from_node, $idx, $visited, $to_nodes) = @_;

    #warn "add edges: $from_node->{idx} => $idx";
    my $bc = $bytecodes[$idx];
    return unless defined $bc;

    my $opcode = opcode($bc);
    if (exists $visited->{$idx}) {
        if ($opcode eq 'split') {
            my $y = $bc->[2];
            if (!$visited->{$y}) {
                local @_ = ($from_node, $y, $visited, $to_nodes);
                goto \&add_nfa_edges;
            }
        }
        return;
    }

    $visited->{$idx} = 1;

    if ($opcode eq 'jmp') {
        local @_ = ($from_node, $bc->[1], $visited, $to_nodes);
        goto \&add_nfa_edges;
    }

    if ($opcode eq 'split') {
        my $x = $bc->[1];
        my $y = $bc->[2];
        my $forked = $to_nodes ? [@$to_nodes] : undef;
        add_nfa_edges($from_node, $x, $visited, $to_nodes);
        local @_ = ($from_node, $y, $visited, $forked);
        goto \&add_nfa_edges;
    }

    if ($opcode eq 'save' or $opcode eq 'assert') {
        #warn Dumper \$bc;
        if (!defined $to_nodes) {
            $to_nodes = [];
        }
        push @$to_nodes, $idx;
        local @_ = ($from_node, $idx + 1, $visited, $to_nodes);
        goto \&add_nfa_edges;
    }

    if (!defined $to_nodes) {
        $to_nodes = [];
    }
    push @$to_nodes, $idx;

    my $edge = $to_nodes;
    {
        my $key = $from_node->{idx} . "-" . $edge->[0];
        #warn $key;
        $nfa_paths{$key} = 1;
    }
    push @{ $from_node->{edges} }, $edge;
}

sub opcode ($) {
    my ($bc) = @_;
    return ref $bc ? $bc->[0] : $bc;
}

sub is_node ($) {
    my ($bc) = @_;
    my $opcode = opcode($bc);
    if ($opcode =~ /^(?:char|notin|in|any|match)$/) {
        return $opcode;
    }
    undef;
}

sub gen_nfa_edge_label ($) {
    my ($e) = @_;
    my @labels;
    for my $idx (@$e) {
        my $bc = $bytecodes[$idx];
        my $opcode = opcode($bc);
        my $label = $cached_labels{$bc};
        if (!defined $label) {
            my $v = ref $bc ? $bc->[1] : undef;
            if ($opcode eq 'assert') {
                $label = $v;
            } elsif ($opcode eq 'any') {
                $label = 'any';
            } elsif ($opcode eq 'char') {
                $label = "'" . escape_char($v) . "'";
            } elsif ($opcode eq 'in') {
                my @args = @$bc;
                shift @args;
                $label = escape_range(\@args, 0);
            } elsif ($opcode eq 'notin') {
                my @args = @$bc;
                shift @args;
                $label = escape_range(\@args, 1);
            } elsif ($opcode eq 'save') {
                my $i = int($v / 2);
                my $sym = $v % 2 == 0 ? '(' : ')';
                $label = "$sym$i";
            } elsif ($opcode eq 'match') {
                $label = "";
            } else {
                die "unknown opcode: $opcode";
            }

            $cached_labels{$bc} = $label;
        }
        $label =~ s/\\/\\\\/g;
        push @labels, $label;
    }
    return join " ", @labels;
}

sub escape_char ($) {
    my ($code) = @_;
    my $c = chr($code);
    my $escaped = $escaped_chars{$c};
    if (defined $escaped) {
        $escaped =~ s/\\/\\\\/g;
        return $escaped;
    }
    if ($c =~ /[[:alnum:]]/) {
        return $c;
    }
    if ($c =~ /[[:print:]]/) {
        return $c;
    }
    return sprintf("\\\\x%02x", ord($c));
}

sub escape_range_char ($) {
    my ($code) = @_;
    my $c = chr($code);
    my $escaped = $escaped_range_chars{$c};
    if (defined $escaped) {
        $escaped =~ s{\\}{\\\\}g;
        return $escaped;
    }
    if ($c =~ /[[:alnum:]]/) {
        return $c;
    }
    if ($c =~ /[[:print:]]/) {
        return $c;
    }
    return sprintf("\\\\x%02x", ord($c));
}

sub gen_dfa ($) {
    my ($nfa) = @_;

    my $nfa_nodes = $nfa->{nodes};

    my %incoming_edges;

    my $dfa_node = {
        nfa_nodes => [$nfa_nodes->[0]],
        edges => undef,
        idx => 0,
        start => 1,
        states => [0],
    };
    my @dfa_nodes = ($dfa_node);
    my %dfa_node_hash;
    $dfa_node_hash{'0'} = $dfa_node;
    my $idx = 1;
    my $i = 0;
    while ($i < @dfa_nodes) {
        my $dfa_node = $dfa_nodes[$i];
        my $nfa_nodes = $dfa_node->{nfa_nodes};
        my $dfa_edges;

        if (!defined $nfa_nodes) {
            # must be of the special assert node type
            my $assert_info = $dfa_node->{assert_info};
            my $nfa_edges = $dfa_node->{nfa_edges};
            #die unless defined $assert_info && defined $nfa_edges;
            $dfa_edges = gen_dfa_edges_for_asserts($dfa_node, $assert_info, $nfa_edges,
                                                   \@dfa_nodes, \%dfa_node_hash, \$idx);
            $dfa_node->{edges} = $dfa_edges;
            if ($dfa_node->{accept}) {
                for my $dfa_edge (@$dfa_edges) {
                    $dfa_edge->{target}{accept} = 1;
                }
                delete $dfa_node->{accept};
            }
            $dfa_node = $dfa_nodes[$dfa_node->{orig_source}];

        } else {
            # being a normal DFA node

            my @all_nfa_edges;
            for my $nfa_node (@$nfa_nodes) {
                my $idx = $nfa_node->{idx};
                my $edges = $nfa_node->{edges};
                if ($edges) {
                    push @all_nfa_edges, @$edges;
                }
            }

            $dfa_edges = gen_dfa_edges($dfa_node, \@dfa_nodes, \%dfa_node_hash,
                                       \@all_nfa_edges, $nfa, \$idx);
            $dfa_node->{edges} = $dfa_edges;
        }

        #warn "[0] edges for node ", $dfa_node->{idx}, ": ", scalar @$dfa_edges;
        for my $dfa_edge (@$dfa_edges) {
            if ($used_asserts) {
                # compute incoming edges for nodes.
                my $target = $dfa_edge->{target};
                my $incoming = $incoming_edges{$target};
                if (defined $incoming) {
                    push @$incoming, $dfa_edge;
                } else {
                    $incoming_edges{$target} = [$dfa_edge];
                }
            }

            # fix the path mappings in the DFA edges

            calc_capture_mapping($dfa_node, $dfa_edge);
            my $shadowing = $dfa_edge->{shadowing};
            if (defined $shadowing) {
                calc_capture_mapping($dfa_node, $shadowing);
            }
        }

        #warn "DFA node ", gen_dfa_node_label($dfa_node), "\n";
        $i++;
    }

    for my $dfa_node (@dfa_nodes) {
        # compute assertion attributes for each DFA node.
        my $incoming = $incoming_edges{$dfa_node};
        my $left_is_word;  # 1 means always word, 0 always nonword, and -1 uncertain
        for my $dfa_edge (@$incoming) {
            my $ranges = $dfa_edge->{char_ranges};
            if (defined $ranges) {
                for (my $i = 0; $i < @$ranges; $i += 2) {
                    my ($a, $b) = ($ranges->[$i], $ranges->[$i + 1]);
                    my $s = join "", chr($a) .. chr($b);
                    if (!defined $left_is_word || $left_is_word != -1) {
                        my $s = join "", chr($a) .. chr($b);
                        if ($s =~ /^\w+$/) {
                            $left_is_word = !defined $left_is_word || $left_is_word == 1 ? 1 : -1;
                        } elsif ($s =~ /^\W+$/) {
                            $left_is_word = !defined $left_is_word || $left_is_word == 0 ? 0 : -1;
                        } else {
                            $left_is_word = -1;
                        }
                    }
                }
            }
        }

        if (defined $left_is_word) {
            $dfa_node->{left_is_word} = $left_is_word;
            if ($left_is_word != -1) {
                #warn "Found node $dfa_node->{idx} whose left char is always a ",
                #$left_is_word ? "" : "non", "word";
            }
        }
    }

    return {
        nodes           => \@dfa_nodes,
        nvec            => $nfa->{nvec},
        incoming_edges  => \%incoming_edges,
    };
}

sub calc_capture_mapping ($$) {
    my ($from_node, $dfa_edge) = @_;
    my $nfa_edges = $dfa_edge->{nfa_edges};
    my $src_states = $from_node->{states};
    my (@mappings, %assigned);
    my $from_row = 0;
    #warn "source state: ", join(",", @$src_states), " => ", gen_dfa_node_label($dfa_edge->{target}), "\n";
    for my $src_state (@$src_states) {
        my $to_row = 0;
        for my $nfa_edge (@$nfa_edges) {
            my $to_pc = $nfa_edge->[0];
            my $key = "$src_state-$to_pc";
            if (!$assigned{$to_row} && $nfa_paths{$key}) {
                #warn "  mapping: $from_row => $to_row\n";
                push @mappings, [$from_row, $to_row];
                $assigned{$to_row} = 1;
            }
            $to_row++;
        }
        $from_row++;
    }
    $dfa_edge->{capture_mappings} = \@mappings;
}

sub gen_dfa_edges_for_asserts ($$$$$$) {
    my ($from_node, $assert_info, $nfa_edges, $dfa_nodes, $dfa_node_hash, $idx_ref) = @_;
    my $assert_nfa_edges = $assert_info->{assert_nfa_edges};
    my $uniq_assert_cnt = $assert_info->{uniq_assert_cnt};
    my $asserts = $assert_info->{asserts};
    # split the DFA edge according to assertions' on/off combinations
    my @dfa_edges;
    my $max_encoding = 2 ** $uniq_assert_cnt - 1;
    for (my $comb_encoding = 0; $comb_encoding <= $max_encoding; $comb_encoding++) {
        my @filtered_nfa_edges;
        my $row = 0;
        for my $e (@$nfa_edges) {
            my $mask = $assert_nfa_edges->[$row++];
            if (defined $mask) {
                if ($comb_encoding & $mask) {
                    push @filtered_nfa_edges, $e;
                }

                # otherwise discard the edge
                #warn gen_dfa_node_label($from_node), ": $mask: discarding edge @$e\n";

            } else {
                # being an edge w/o assertions
                push @filtered_nfa_edges, $e;
            }
        }
        if (!@filtered_nfa_edges) {
            # not possible
            next;
        }
        $from_node->{max_assert_settings} = $max_encoding;
        my $dfa_edge = {
            assert_settings => $comb_encoding,
            nfa_edges => reorder_nfa_edges(\@filtered_nfa_edges, undef),
        };
        push @dfa_edges, $dfa_edge;
    }

    #warn "dfa_edges: ", Dumper(\@dfa_edges);

    my %targets;
    for my $dfa_edge (@dfa_edges) {
        $dfa_edge = resolve_dfa_edge(undef, $dfa_edge, undef, \%targets,
                                     $dfa_nodes, $dfa_node_hash, $idx_ref, 1);
    }

    @dfa_edges = grep { defined } @dfa_edges;

    return \@dfa_edges;
}

sub gen_dfa_edges ($$$$$$) {
    my ($from_node, $dfa_nodes, $dfa_node_hash, $nfa_edges, $nfa, $idx_ref) = @_;

    my (%left_end_hash, %right_end_hash, %prio, @endpoints);

    # process char ranges

    #warn "node: ", gen_dfa_node_label($from_node);
    #warn "  NFA edges: ", Dumper($nfa_edges);

    my $prio = 0;
    my (@accept_edges, $in_shadow, %shadowed_nfa_edges);
    for my $nfa_edge (@$nfa_edges) {
        $prio{$nfa_edge} = $prio++;

        if ($in_shadow) {
            $shadowed_nfa_edges{$nfa_edge} = 1;
        }

        my $to = $nfa_edge->[-1];
        my $bc = $bytecodes[$to];
        my $opcode = opcode($bc);
        #warn "opcode: $opcode";
        if ($opcode eq 'any') {
            my ($a, $b) = (0, 255);
            push @endpoints, $a, $b;
            add_to_hash(\%left_end_hash, $a, $nfa_edge);
            add_to_hash(\%right_end_hash, $b, $nfa_edge);
        } elsif ($opcode eq 'char') {
            my $a = $bc->[-1];
            push @endpoints, $a;
            add_to_hash(\%left_end_hash, $a, $nfa_edge);
            add_to_hash(\%right_end_hash, $a, $nfa_edge);
        } elsif ($opcode eq 'in') {
            my @args = @$bc;
            shift @args;
            #canon_range(\@args);
            #warn "args: ", Dumper(\@args);
            for (my $i = 0; $i < @args; $i += 2) {
                my ($a, $b)  = ($args[$i], $args[$i + 1]);
                push @endpoints, $a, $b;
                add_to_hash(\%left_end_hash, $a, $nfa_edge);
                add_to_hash(\%right_end_hash, $b, $nfa_edge);
            }
        } elsif ($opcode eq 'notin') {
            my @args = @$bc;
            shift @args;
            #canon_range(\@args);
            #warn "args: ", Dumper(\@args);
            my $from = 0;
            my $found = 0;
            for (my $i = 0; $i < @args; $i += 2) {
                my ($a, $b)  = ($args[$i], $args[$i + 1]);
                if ($from <= $a - 1) {
                    push @endpoints, $from;
                    push @endpoints, $a - 1;
                    add_to_hash(\%left_end_hash, $from, $nfa_edge);
                    add_to_hash(\%right_end_hash, $a - 1, $nfa_edge);
                }
                $from = $b + 1;
                $found++;
            }
            if ($found && $from <= 255) {
                push @endpoints, $from;
                push @endpoints, 255;
                add_to_hash(\%left_end_hash, $from, $nfa_edge);
                add_to_hash(\%right_end_hash, 255, $nfa_edge);
            }
        } elsif ($opcode eq 'match') {
            #warn "Found match: @$nfa_edge";
            push @accept_edges, $nfa_edge;
            my $found_asserts;
            for my $pc (@$nfa_edge) {
                if ($pc2assert{$pc}) {
                    $found_asserts = 1;
                    last;
                }
            }
            #last;
            if (!$found_asserts) {
                #warn "no assertions found. short-cutting";
                last;
            }
            # the remaining NFA edges are shadowed by this to-accept NFA edge
            # with assertins.
            #if (defined $in_shadow) {
                #die "TODO: nested shadows";
            #}
            $in_shadow = 1;
        } else {
            die "unknown bytecode opcode: $opcode";
        }
    }
    @endpoints = uniq sort { $a <=> $b } @endpoints;

    #warn "accept edges: ", Dumper(\@accept_edges);
    #warn "left endpoint hash: ", Dumper(\%left_end_hash);
    #warn "right endpoint hash: ", Dumper(\%right_end_hash);
    #warn "endpoints: ", Dumper(\@endpoints);

    # split and merge char ranges to form DFA edges

    my (@active_nfa_edges, @dfa_edges, $prev);
    for my $p (@endpoints) {
        if (!@active_nfa_edges) {
            die if defined $prev;
            $prev = $p;
            my $left_nfa_edges = $left_end_hash{$p};
            if (!defined $left_nfa_edges) {
                #warn $p;
                die;
            }
            add_to_set(\@active_nfa_edges, $left_nfa_edges);

            my $right_nfa_edges = $right_end_hash{$p};
            if (defined $right_nfa_edges) {
                # singular
                push @dfa_edges, gen_dfa_edge($prev, $p, \@active_nfa_edges,
                                              \%prio, \%shadowed_nfa_edges);
                remove_from_set(\@active_nfa_edges, $right_nfa_edges);
                if (@active_nfa_edges) {
                    $prev++;
                } else {
                    undef $prev;
                }
            }

        } else {
            # pending right endpoint
            die unless defined $prev;

            my $right_nfa_edges = $right_end_hash{$p};
            my $left_nfa_edges = $left_end_hash{$p};

            if (defined $right_nfa_edges && defined $left_nfa_edges) {
                if ($prev <= $p - 1) {
                    push @dfa_edges, gen_dfa_edge($prev, $p - 1,
                                                  \@active_nfa_edges, \%prio,
                                                  \%shadowed_nfa_edges);
                }
                add_to_set(\@active_nfa_edges, $left_nfa_edges);
                push @dfa_edges, gen_dfa_edge($p, $p, \@active_nfa_edges, \%prio,
                                              \%shadowed_nfa_edges);
                remove_from_set(\@active_nfa_edges, $right_nfa_edges);
                if (!@active_nfa_edges) {
                    undef $prev;
                } else {
                    $prev = $p + 1;
                }

            } elsif (defined $right_nfa_edges) {
                push @dfa_edges, gen_dfa_edge($prev, $p, \@active_nfa_edges,
                                              \%prio, \%shadowed_nfa_edges);
                remove_from_set(\@active_nfa_edges, $right_nfa_edges);
                if (!@active_nfa_edges) {
                    undef $prev;
                } else {
                    $prev = $p + 1;
                }

            } elsif (defined $left_nfa_edges) {
                if ($prev <= $p - 1) {
                    push @dfa_edges, gen_dfa_edge($prev, $p - 1,
                                                  \@active_nfa_edges, \%prio,
                                                  \%shadowed_nfa_edges);
                }
                add_to_set(\@active_nfa_edges, $left_nfa_edges);
                $prev = $p;
            }
        }
    }

    # resolve DFA edge targets

    if (@accept_edges) {
        my $accept_dfa_edge = gen_dfa_edge(undef, undef, \@accept_edges, \%prio, undef);
        unshift @dfa_edges, $accept_dfa_edge;
    }

    #if ($from_node->{idx} == 2) {
        #warn "DFA edges: ", Dumper(\@dfa_edges);
    #}

    #warn "One group";

    my %targets;
    for my $dfa_edge (@dfa_edges) {
        $dfa_edge = resolve_dfa_edge($from_node, $dfa_edge, \@accept_edges, \%targets,
                                     $dfa_nodes, $dfa_node_hash, $idx_ref, 0);
        next unless defined $dfa_edge;
        if ($dfa_edge->{shadowed}) {
            $dfa_edge = undef;
            next;
        }
    }

    @dfa_edges = grep { defined } @dfa_edges;

    #warn "count chars in edges";
    for my $dfa_edge (@dfa_edges) {
        $dfa_edge->{nchars} = count_chars_in_ranges($dfa_edge->{char_ranges});
        #warn "nchars: ", $dfa_edge->{nchars};
    }

    @dfa_edges = sort { $a->{nchars} <=> $b->{nchars} } @dfa_edges;

    #warn "show char count in shorted edges";
    #for my $dfa_edge (@dfa_edges) {
        #warn "nchars: ", $dfa_edge->{nchars};
    #}

    {
        my @total_ranges;
        for my $dfa_edge (@dfa_edges) {
            my $range = $dfa_edge->{char_ranges};
            if (defined $range) {
                push @total_ranges, @$range;
            }
        }

        if (@total_ranges) {
            canon_range(\@total_ranges);
            #warn "canon total range: @total_ranges";
            if (@total_ranges == 2 && $total_ranges[0] == 0 && $total_ranges[1] == 255) {
                $dfa_edges[-1]->{default_branch} = 1;
            }
        }
    }

    #warn "DFA edges: ", Dumper(\@dfa_edges);
    return \@dfa_edges;
}

sub resolve_dfa_edge ($$$$$$$$) {
    my ($from_node, $dfa_edge, $accept_edges, $targets, $dfa_nodes, $dfa_node_hash, $idx_ref, $no_assert_check) = @_;
    my $nfa_edges = $dfa_edge->{nfa_edges};
    my $assert_info;
    if (!$no_assert_check) {
        $assert_info = resolve_asserts($nfa_edges);
        #warn "assert info: ", Dumper($assert_info);
    }
    #warn "DFA edge target: ", Dumper($nfa_edges);

    if (!defined $assert_info) {
        $nfa_edges = dedup_nfa_edges($nfa_edges);
        $dfa_edge->{nfa_edges} = $nfa_edges;
    }

    my @states;
    for my $nfa_edge (@$nfa_edges) {
        push @states, $nfa_edge->[-1];
    }

    my ($key, $target_dfa_node);
    if (!defined $assert_info) {
        $key = gen_dfa_hash_key(\@states, $dfa_edge);
        #warn "dfa state key: ", $key;
        my $old_edge = $targets->{$key};
        if (defined $old_edge) {
            my $old_ranges = $old_edge->{char_ranges};
            if (defined $old_ranges) {
                my $cur_ranges = $dfa_edge->{char_ranges};
                #warn "old_ranges: $old_ranges; cur_ranges: $cur_ranges";
                push @$old_ranges, @$cur_ranges;
                return undef;
            }
        }
        $targets->{$key} = $dfa_edge;
        #warn "looking up key $key";
        $target_dfa_node = $dfa_node_hash->{$key};
        if (defined $target_dfa_node) {
            $dfa_edge->{target} = $target_dfa_node;
            return $dfa_edge;
        }
    }

    my $is_accept;
    if ($accept_edges && @$accept_edges && @$nfa_edges == @$accept_edges
        && "@$nfa_edges" eq "@$accept_edges")
    {
        $is_accept = 1;
    }

    my $nfa_nodes;
    if (!defined $assert_info) {
        $nfa_nodes = [];
        for my $nfa_edge (@$nfa_edges) {
            my $nfa_idx = $nfa_edge->[-1];
            my $nfa_node = first { $_->{idx} eq $nfa_idx } @{ $nfa->{nodes} };
            push @$nfa_nodes, $nfa_node;
        }
    }
    $target_dfa_node = {
        defined $assert_info
            ? (assert_info => $assert_info,
               orig_source => $from_node->{idx},
               nfa_edges => $nfa_edges)
            : (nfa_nodes => $nfa_nodes),
        edges => undef,
        states => \@states,
        idx => $$idx_ref++,
        $is_accept ? (accept => 1) : (),
    };
    #if ($target_dfa_node->{idx} == 319) {
    #warn "from node: ", Dumper($from_node);
    #die "dfa edge: ", Dumper($dfa_edge);
    #}
    push @$dfa_nodes, $target_dfa_node;
    if (!defined $assert_info) {
        $dfa_node_hash->{$key} = $target_dfa_node;
    }
    $dfa_edge->{target} = $target_dfa_node;
    return $dfa_edge;
}

# may return two DFA edges in case of shadow splitting
sub gen_dfa_edge ($$$$$) {
    my ($a, $b, $nfa_edges, $nfa_edge_prio, $shadowed_nfa_edges) = @_;

    if (!defined $shadowed_nfa_edges) {
        #my $prio_range = gen_dfa_edge_prio_range($nfa_edges, $nfa_edge_prio);
        if (defined $a) {
            my $nfa_edges = reorder_nfa_edges($nfa_edges, $nfa_edge_prio);
            return {
                char_ranges => [$a, $b],
                nfa_edges => $nfa_edges,
                #prio_range => $prio_range,
            };
        }
        return {
            to_accept => 1,
            nfa_edges => $nfa_edges,
            #prio_range => $prio_range,
        };
    }

    # try to split the DFA edge if there are shadowed NFA edges mixed.

    my (@unshadowed);
    for my $nfa_edge (@$nfa_edges) {
        my $v = $shadowed_nfa_edges->{$nfa_edge};
        if (!$v) {
            push @unshadowed, $nfa_edge;
        }
    }

    if (@unshadowed == @$nfa_edges) {
        local @_ = ($a, $b, $nfa_edges, $nfa_edge_prio, undef);
        goto \&gen_dfa_edge;
    }

    if (@unshadowed == 0) {
        my $dfa_edge = gen_dfa_edge($a, $b, $nfa_edges, $nfa_edge_prio, undef);
        $dfa_edge->{check_to_accept_sibling} = 1;
        return $dfa_edge;
    }

    #warn "found shadowed! ", scalar @unshadowed, " vs ", scalar @$nfa_edges;

    # generate two DFA edges, one shadowing the other according to the result
    # of the assertions on the shadowing DFA edge (the to-accept edge).
    my $wide_dfa_edge = gen_dfa_edge($a, $b, $nfa_edges, $nfa_edge_prio, undef);
    my $narrow_dfa_edge = gen_dfa_edge($a, $b, \@unshadowed, $nfa_edge_prio, undef);
    $narrow_dfa_edge->{shadowing} = $wide_dfa_edge;
    #delete $wide_dfa_edge->{char_ranges};
    $wide_dfa_edge->{shadowed} = 1;
    return $narrow_dfa_edge, $wide_dfa_edge;
}

sub resolve_asserts ($) {
    my ($nfa_edges) = @_;

    # categorize NFA edges according to with assertions and without assertions

    my (@assert_nfa_edges, %asserts);
    my $assert_idx = 0;
    my $row = 0;
    for my $nfa_edge (@$nfa_edges) {
        my $found;
        my $mask = 0;
        for my $pc (@$nfa_edge) {
            my $assert = $pc2assert{$pc};
            next unless defined $assert;
            $found = 1;
            my $idx = $asserts{$assert};
            if (!defined $idx) {
                $idx = $assert_idx++;
                #warn "assert $assert not found, assigned a new index $idx";
                $asserts{$assert} = $idx;
            } else {
                #warn "assert $assert found existing index $idx";
            }
            $mask |= 1 << $idx;
            #warn "mask: $mask";
        }
        if ($found) {
            $assert_nfa_edges[$row] = $mask;
        }
        $row++;
    }

    #warn $assert_idx;

    if ($assert_idx) {
        #warn "asserts: ", Dumper(%asserts);
        return {
            assert_nfa_edges => \@assert_nfa_edges,
            uniq_assert_cnt => $assert_idx,
            asserts => \%asserts,
        };
    }

    return undef;
}

sub canon_range ($) {
    my ($args) = @_;
    my (%left_end_hash, %right_end_hash, @endpoints);
    for (my $i = 0; $i < @$args; $i += 2) {
        my ($a, $b)  = ($args->[$i], $args->[$i + 1]);
        push @endpoints, $a, $b;
        $left_end_hash{$a}++;
        $right_end_hash{$b}++;
    }
    @endpoints = uniq sort { $a <=> $b } @endpoints;
    my @new;
    my $cnt = 0;
    my $prev;
    for my $p (@endpoints) {
        my $new_prev;
        my $c1 = $left_end_hash{$p};
        if (defined $c1) {
            $cnt += $c1;
        }
        my $c2 = $right_end_hash{$p};
        if (defined $c2) {
            $cnt -= $c2;
        }
        if ($cnt == 0) {
            if (defined $prev) {
                push @new, $prev, $p;
                undef $prev;
            } else {
                # singular
                push @new, $p, $p;
            }
        } else {
            if (!defined $prev) {
                $prev = $p;
            }
        }
    }
    if (@new > 2) {
        my @new2;
        push @new2, $new[0];
        my $prev = $new[1];
        my $found;
        for (my $i = 2; $i < @new; $i += 2) {
            my $cur = $new[$i];
            if ($cur == $prev + 1) {
                # swallow up the previous (left) end point and the current (right) end point
                $found = 1;
            } else {
                push @new2, $prev, $cur;
            }
            $prev = $new[$i + 1];
        }
        if ($found) {
            push @new2, $prev;
            @new = @new2;
        }
    }
    @$args = @new;
}

sub reorder_nfa_edges ($$) {
    my ($nfa_edges, $nfa_edge_prio) = @_;
    my @edges = defined $nfa_edge_prio
                ?  sort { $nfa_edge_prio->{$a} <=> $nfa_edge_prio->{$b} } @$nfa_edges
                : @$nfa_edges;
    return \@edges;
}

sub dedup_nfa_edges ($) {
    my ($nfa_edges) = @_;
    my %visited;
    my @ret;
    for my $e (@$nfa_edges) {
        my $last = $e->[-1];
        if ($visited{$last}) {
            next;
        }
        my $bc = $bytecodes[$last];
        #warn "opcode: ", opcode($bc);
        if (opcode($bc) eq 'match') {
            push @ret, $e;
            #warn "short-circuiting...";
            last;
        }
        $visited{$last} = 1;
        push @ret, $e;
    }
    return \@ret;
}

sub gen_dfa_hash_key ($$) {
    my ($states, $dfa_edge) = @_;
    #carp "nfa edges: ", Dumper($nfa_edges);

    # FIXME: we should distinguish different shadowing groups here
    # currently this issue can be exposed by gcc's -Wunused-label warnings.

    my $shadowing = $dfa_edge->{shadowing};
    my $key = (defined $shadowing ? "2-" : $dfa_edge->{shadowed} ? '1-' : '0-')
           . join ",", @$states;
    #warn $key;
    return $key;
}

sub add_to_set ($$) {
    my ($set1, $set2) = @_;
    for my $b (@$set2) {
        if (!defined first { $_ eq $b } @$set1) {
            push @$set1, $b;
        }
    }
}

sub remove_from_set ($$) {
    my ($set1, $set2) = @_;
    my $found = 0;
    for my $b (@$set2) {
        my $idx = firstidx { $_ eq $b } @$set1;
        if (defined $idx && $idx >= 0) {
            splice @$set1, $idx, 1;
            $found++;
        }
    }
    return $found;
}

sub add_to_hash ($$) {
    my ($hash, $k, $v) = @_;
    if (!defined $k) {
        croak "No key defined";
    }
    my $oldv = $hash->{$k};
    if (defined $oldv) {
        push @$oldv, $v;
    } else {
        $hash->{$k} = [$v];
    }
}

sub draw_dfa ($) {
    my ($dfa) = @_;

    my $graph = GraphViz->new(
        layout => $big ? 'twopi' : 'neato',
        ratio => 'auto',
        node => $node_attr,
        edge => $edge_attr,
    );

    my $dfa_nodes = $dfa->{nodes};

    for my $node (@$dfa_nodes) {
        my $idx = $node->{idx};
        my $label = gen_dfa_node_label($node);
        $graph->add_node("n$idx", $node->{start} ? (color => 'orange') : (),
                         $node->{assert_info} ? (fillcolor => 'orange') : (),
                         $node->{accept} ? (shape => 'doublecircle') : (),
                         label => $big ? '' : $label || " " . $label);
    }

    for my $node (@$dfa_nodes) {
        my $from_idx = $node->{idx};
        for my $e (@{ $node->{edges} }) {
            my $label = gen_dfa_edge_label($node, $e);
            my $to = $e->{target};
            my $to_idx = $to->{idx};
            $graph->add_edge("n$from_idx" => "n$to_idx", label => $label,
                             len => max(length($label) / 6, 1.7));
            my $shadowing = $e->{shadowing};
            if (defined $shadowing) {
                #my $label = gen_dfa_edge_label($node, $shadowing);
                my $to = $shadowing->{target};
                my $to_idx = $to->{idx};
                $graph->add_edge("n$from_idx" => "n$to_idx", label => $label,
                                 len => max(length($label) / 6, 1.7),
                                 style => 'dashed');
            }
        }
    }

    $graph->as_png("dfa.png");
}

sub gen_dfa_edge_label ($$) {
    my ($from_node, $edge) = @_;
    my $assert_settings = $edge->{assert_settings};
    if (defined $assert_settings) {
        # must be the assert results
        my $assert_info = $from_node->{assert_info} or die;
        my $asserts = $assert_info->{asserts} or die;
        my @labels;
        for my $assert (sort keys %$asserts) {
            my $idx = $asserts->{$assert};
            (my $label = $assert) =~ s/\\/\\\\/g;
            if (!($assert_settings & (1 << $idx))) {
                $label = "!$label";
            }
            push @labels, $label;
        }
        #warn "labels: @labels";
        return join ",", @labels;
    }
    if ($edge->{to_accept}) {
        # epsilon edge to an "accept" state
        return "ɛ";
    }
    my $ranges = $edge->{char_ranges};
    #warn "range size: ", scalar @bits;
    return escape_range($ranges, 0);
}

sub gen_dfa_node_label ($) {
    my ($node) = @_;
    #if ($node->{start}) {
    #return "0";
    #}
    my @lines = "{" . join(",", @{ $node->{states} }) . "}";
    push @lines, "[" . $node->{idx} . "]";
    if (defined $node->{min_len}) {
        push @lines, "∧=$node->{min_len}";
    }
    return join "\\n", @lines;
}

sub escape_range ($$) {
    my ($range, $negate) = @_;
    if (!defined $range) {
        croak;
    }
    my $s;
    if ($negate) {
        $s = "[^";
    } else {
        if (@$range == 2) {
            if ($range->[0] == $range->[1]) {
                return "'" . escape_char($range->[0]) . "'";
            }
        }
        $s = "[";
    }
    #warn "range: ", Dumper($range);
    for (my $i = 0; $i < @$range; $i += 2) {
        my $a = $range->[$i];
        my $b = $range->[$i + 1];
        if (!defined $b) {
            croak @$range;
        }
        if ($a == $b) {
            $s .= escape_range_char($a);
        } else {
            $s .= escape_range_char($a) . "-" . escape_range_char($b);
        }
    }
    $s .= "]";
}

sub gen_c_from_dfa ($) {
    my ($dfa) = @_;

    my $nvec = $dfa->{nvec};
    #die "nvec: $nvec";

    if (!$global) {
        $global = 0;
    }

    my $infile = "$FindBin::Bin/bench/getcputime.h";
    open my $in, $infile
        or die "cannot open $infile for reading: $!\n";
    my $getcputime = do { local $/; <$in> };
    close $in;

    my $src = <<_EOC_;
#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <errno.h>
#include <time.h>
#include <string.h>

$getcputime

#if __GNUC__ > 3
#    define likely(x)       __builtin_expect((x),1)
#    define unlikely(x)     __builtin_expect((x),0)
#else
#    define likely(x)      (x)
#    define unlikely(x)    (x)
#endif

#define u_char          unsigned char


enum {
    NO_MATCH = 0,
    MATCHED  = 1,
    BUFSIZE = 4096
};


static int match(const u_char *const s, size_t len, int *const ovec);


static inline int
is_word(int c)
{
    /* (isalnum(c) || c == '_'); */
    switch (c) {
_EOC_

    for my $c ('0' .. '9', 'A' .. 'Z', 'a' .. 'z', '_') {
        $src .= "    case '$c':\n";
    }

    $src .= <<_EOC_;
        return 1;
    default:
        return 0;
    }
}


static inline int
is_word_boundary(int a, int b)
{
    return (is_word(a) ^ is_word(b));
}


int
main(void)
{
    int          i, rc, ovec[$nvec], global = $global, matches;
    char        *p, *buf;
    size_t       len, bufsize, rest;
    double       best = -1;

    buf = malloc(BUFSIZE);
    if (buf == NULL) {
        perror("malloc");
        exit(1);
    }

    p = buf;
    len = 0;
    bufsize = BUFSIZE;
    rest = BUFSIZE;

    do {
        rc = fread(p, 1, rest, stdin);
        if (rc < rest) {
            if (ferror(stdin)) {
                perror("fread");
                exit(1);
            }

            /* must have reached eof */
            len += rc;
            break;
        }

        /* rc == rest */

        len += rc;

        if (feof(stdin)) {
            p += rc;
            break;
        }

        /* grow the buffer */
        rest = bufsize;
        bufsize <<= 1;
        buf = realloc(buf, bufsize);
        if (buf == NULL) {
            perror("malloc");
            exit(1);
        }

        p = buf + len;
    } while (1);

    /*
    if ($debug == 2) {
        fprintf(stderr, "input string: %.*s\\n", (int) len, buf);
    }
    */

    printf("SRegex DFA proto ");

    /* memset(ovec, -1, sizeof(ovec)/sizeof(ovec[0])); */

    {
        size_t      rest;

        for (i = 0; i < $repeat; i++) {
            double               elapsed, begin, end;

            matches = 0;
            p = buf;
            rest = len;

            if ($timer) {
                begin = get_cpu_time();
                if (begin == -1) {
                    perror("get_cpu_time");
                    exit(2);
                }
            }

            do {
                rc = match((u_char *) p, rest, ovec);

                if (rc > 0) {
                    matches++;
                    p += ovec[1];
                    rest -= ovec[1];
                }

            } while (global && rc > 0);

            if ($timer) {
                end = get_cpu_time();
                if (end == -1) {
                    perror("get_cpu_time");
                    exit(2);
                }
                elapsed = end - begin;

                if (i == 0 || elapsed < best) {
                    best = elapsed;
                }
            }
        }
    }

    if (rc == NO_MATCH) {
        printf("no match");

    } else {
        printf("match");
        for (i = 0; i < $nvec; i += 2) {
            printf(" (%d, %d)", ovec[i], ovec[i + 1]);
        }
    }

    if (best != -1) {
        printf(": %.05lf ms elapsed (%d matches found, $repeat repeated times).\\n",
               best * 1e3, matches);

    } else {
        printf("\\n");
    }

    return 0;
}


static int
match(const u_char *const s, size_t len, int *const ovec)
{
    int c;
    int i = 0;
_EOC_

    {
        for (my $i = 0; $i < $nvec; $i++) {
            $src .= "    int matched_$i = -1;\n";
        }
    }

    my $dfa_nodes = $dfa->{nodes};

    my $max_threads = 0;
    for my $node (@$dfa_nodes) {
        my $n = @{ $node->{states} };
        if ($n > $max_threads) {
            $max_threads = $n;
        }
    }

    $src .= "    /* for maximum $max_threads threads */\n";
    for (my $i = 0; $i < $max_threads; $i++) {
        for (my $j = 0; $j < $nvec; $j++) {
            my $var = "caps${i}_$j";
            $src .= "    int $var = -1;\n";
        }
    }

    for my $node (@$dfa_nodes) {
        next if defined $node->{assert_info} || $node->{accept};
        $src .= gen_c_from_dfa_node($node, $nvec);
    }

    $src .= <<"_EOC_";
}
_EOC_
    return $src;
}

sub gen_c_from_dfa_node ($$) {
    my ($node, $nvec) = @_;
    my $idx = $node->{idx};

    my $level = 1;
    my $src = '';

    my $label = gen_dfa_node_label($node);
    $label =~ s/\\n/ /g;

    if ($idx != 0) {
        $src .= "\nst$idx: {  /* DFA node $label */\n";
    } else {
        $src .= "\n    {  /* DFA node $label */\n";
    }

    my $edges = $node->{edges};

    $src .= qq{    fprintf(stderr, "entering state $label\\n");\n} if $debug;

    my $used_error;

    if (@$edges == 2) {
        # try to apply memchr optimization
        my ($a, $b) = @$edges;
        my $a_ranges = $a->{char_ranges};
        if (!$a->{to_accept}
            && @$a_ranges == 2
            && $a_ranges->[0] == $a_ranges->[1]
            && !defined $a->{target}{assert_info}
            && $b->{default_branch}
            && $b->{target} eq $node)
        {
            #warn "HIT: $re: $idx: ", gen_dfa_edge_label($node, $a);
            my $chr = $a_ranges->[0];

            $b->{memchr} = 1;
            my ($b_src) = gen_c_from_dfa_edge($node, $b, $level, $nvec, undef);
            delete $b->{memchr};

            $src .= <<_EOC_;
    {
        /* shortcut: search for a single char */
        const u_char *p;

        p = (const u_char *) memchr(s + i, $chr, len - i);
        if (unlikely(p == NULL)) {
            i = len;
            goto st${idx}_error;
        }

        i = p - s;
    }
_EOC_
            $used_error = 1;

            $src .= $b_src;

            $src .= <<_EOC_;
    i++;
    c = $chr;
_EOC_
            $a->{default_branch} = 1;
            my ($a_src) = gen_c_from_dfa_edge($node, $a, $level, $nvec, undef);
            delete $a->{default_branch};
            $src .= $a_src;

            goto closing_state;
        }
    }

    my $use_switch;
    if (@$edges >= 2) {
        # try to apply switch/case optimization
        my $count = 0;
        my $threshold = 100;
        #warn "edges for node ", $node->{idx}, ": ", scalar @$edges;
        for my $edge (@$edges) {
            my $ranges = $edge->{char_ranges};
            if (defined $ranges) {
                #warn "check edge ", gen_dfa_edge_label($node, $edge), " w/ ",
                    #scalar @$ranges, " ranges";
                #warn "ranges: @$ranges";
                my $nchars = $edge->{nchars};
                if ($count + $nchars <= $threshold) {
                    $count += $nchars;
                    $edge->{use_case} = 1;
                    next;
                }
            }
            last;
        }
        #warn "$count";
        if ($count >= 2 && $count <= $threshold) {
            #warn "HIT $count";
            $use_switch = 1;
        }
    }

    #undef $use_switch;

    my $to_accept;

    if (@$edges) {
        if ($edges->[0]{to_accept}) {
            $src .= "    c = i < len ? s[i++] : (i++, -1);\n";
            if ($debug) {
                $src .= qq{     fprintf(stderr, "reading new char \\"%d\\"\\n", c);\n};
            }

            $to_accept = 1;

        } else {
            $src .= <<"_EOC_";
    if (unlikely(i >= len)) {
        i++;
        goto st${idx}_error;
    }

    c = s[i++];
_EOC_
            $used_error = 1;

            if ($debug) {
                $src .= qq{    fprintf(stderr, "reading new char \\"%d\\"\\n", c);\n};
            }
        }
    }

    if (!$to_accept && $use_switch) {
        $src .= "    switch (c) {\n";
    }

    my $seen_accept;
    for my $edge (@$edges) {
        my $edge_src;
        ($edge_src, $to_accept, $use_switch) = gen_c_from_dfa_edge($node, $edge, $level, $nvec, $use_switch);

        $src .= $edge_src;

        if ($to_accept) {
            $seen_accept = 1;
        }

        if ($to_accept && @$edges > 1) {
            $src .= "    if (c != -1) {\n";
            if ($use_switch) {
                $src .= "        switch (c) {\n";
            }
            $level++;
        }
    }

    if ($use_switch) {
        $src .= "    default:\n        break;\n    }\n";
    }

    if ($seen_accept && @$edges > 1) {
        $src .= "    }\n";
        $level--;
    }

closing_state:

    $src .= "    }  /* end state */\n\n";

    if ($used_error) {
        $src .= "st${idx}_error:\n";
    }

    my $indent = '';
    if (!$seen_accept) {
        $src .= "    if (matched_0 != -1) {\n";
        $indent = '    ';
    }

    for (my $i = 0; $i < $nvec; $i++) {
        $src .= $indent . "    ovec[$i] = matched_$i;\n";
    }

    $src .= $indent . "    return MATCHED;  /* fallback */\n";

    if (!$seen_accept) {
        $src .= <<'_EOC_';
    }
    return NO_MATCH;
_EOC_
    }

    return $src;
}

sub gen_c_from_dfa_edge ($$$$$) {
    my ($from_node, $edge, $level, $nvec, $use_switch) = @_;

    my $from_node_idx = $from_node->{idx};

    my $src = '';
    my @indents = (" " x (4 * $level), " " x (4 * ($level + 1)));
    my $indent_idx = 0;

    my $ranges = $edge->{char_ranges};
    my $target = $edge->{target};
    my $to_accept = $edge->{to_accept};
    my $default_br = $edge->{default_branch};

    #warn "to accept: $to_accept";

    my $new_use_switch;
    if ($use_switch && !$edge->{use_case}) {
        $src .= $indents[$indent_idx] . "default:\n";
        $src .= $indents[$indent_idx] . "    break;\n";
        $src .= $indents[$indent_idx] . "}\n";
        undef $use_switch;
    } else {
        $new_use_switch = $use_switch;
    }

    my @cond;
    my $right_is_word; # 0 means always not a word, 1 means always a word, and -1 uncertain
    if (defined $ranges && !$edge->{shadowed}) {
        for (my $i = 0; $i < @$ranges; $i += 2) {
            my ($a, $b) = ($ranges->[$i], $ranges->[$i + 1]);

            if (!defined $right_is_word || $right_is_word != -1) {
                my $s = join "", chr($a) .. chr($b);
                if ($s =~ /^\w+$/) {
                    $right_is_word = !defined $right_is_word || $right_is_word == 1 ? 1 : -1;
                } elsif ($s =~ /^\W+$/) {
                    $right_is_word = !defined $right_is_word || $right_is_word == 0 ? 0 : -1;
                } else {
                    $right_is_word = -1;
                }
            }

            if ($use_switch) {
                for my $c ($a .. $b) {
                    push @cond, $c;
                }
            } else {
                if ($a == $b) {
                    push @cond, "c == $a";
                } else {
                    push @cond, "c >= $a && c <= $b";
                }
            }
        }
    }

    #$right_is_word = -1;

    if (@cond) {
        if ($use_switch) {
            if ($default_br) {
                $src .= $indents[$indent_idx] . "default: {\n";
                #$src .= $indents[$indent_idx] . "    /* " . join(", ", @cond) . " */\n";
                undef $new_use_switch;

            } else {
                my $i = 0;
                for my $cond (@cond) {
                    $src .= $indents[$indent_idx] . "case $cond:";
                    if (++$i == @cond) {
                        $src .= " {\n";
                    } else {
                        $src .= "\n";
                    }
                }
            }

            $indent_idx++;

        } else {
            my $cond;
            if (@cond == 1) {
                $cond = $cond[0];
            } else {
                $cond = join " || ", map { "($_)" } @cond;
            }

            if ($default_br) {
                $src .= $indents[$indent_idx] . "/* $cond */\n";
            } else {
                $src .= $indents[$indent_idx] . "if ($cond) {\n";
            }
            $indent_idx++ if !$default_br;
        }

        my $sibling_assert_settings = $edge->{check_to_accept_sibling};
        if (defined $sibling_assert_settings) {
            my $indent = $indents[$indent_idx];
            $src .= $indent . "if (asserts == $sibling_assert_settings) {\n";

            for (my $i = 0; $i < $nvec; $i++) {
                $src .= $indent . "    ovec[$i] = matched_$i;\n";
            }

            $src .= $indent . "    return MATCHED;\n";
            $src .= $indent . "}\n";

        } else {
            my $shadowing = $edge->{shadowing};
            if (defined $shadowing) {
                my $indent = $indents[$indent_idx];
                $src .= $indent . "if (asserts != 1) { /* shadowed DFA edge */\n";
                my ($inner, $to_accept) = gen_c_from_dfa_edge($from_node, $shadowing,
                                                              $level + 2, $nvec, $use_switch);
                if (defined $inner) {
                    $src .= $inner;
                }
                die if $to_accept;
                $src .= $indent . "}\n";
            }
        }
    }

    my $left_is_word = $from_node->{left_is_word};

    my $assert_info = $target->{assert_info};
    my $indent = $indents[$indent_idx];
    if (defined $assert_info) {
        my $asserts = $assert_info->{asserts};
        $src .= $indent . "int asserts = 0;\n";
        my $min_len = $from_node->{min_len} // die;
        for my $assert (sort keys %$asserts) {
            my $idx = $asserts->{$assert};
            if ($assert eq '^') {
                if ($min_len >= 1) {
                    $src .= $indent . 'asserts |= (s[i - 2] == 10) << ' . "$idx;\n";
                } else {
                    $src .= $indent . 'asserts |= (i == 1 || (i >= 2 && s[i - 2] == 10)) << '
                           . "$idx;\n";
                }
            } elsif ($assert eq '$') {
                $src .= $indent . 'asserts |= (c == -1 || c == 10) << ' . "$idx;\n";
            } elsif ($assert eq '\b') {
                #warn "right is word: $right_is_word";
                if (defined $right_is_word && $right_is_word != -1) {
                    #if (defined $left_is_word && $left_is_word != -1) {
                        #warn "HIT! $left_is_word vs $right_is_word";
                    #}

                    if ($right_is_word == 1) {  # left char must not be a word
                        if (defined $left_is_word && $left_is_word != -1) {
                            #warn "HIT";
                            if ($left_is_word == 0) {
                                $src .= "asserts |= " . (1 << $idx) . ";\n";
                            } else {
                                # do nothing, since it's "asserts |= 0;".
                            }

                        } else {
                            if ($min_len >= 1) {
                                $src .= $indent . 'asserts |= !is_word(s[i - 2]) << ' . "$idx;\n";
                            } else {
                                $src .= $indent . 'asserts |= (i >= 2 ? !is_word(s[i - 2]) : 1) << '
                                       . "$idx;\n";
                            }
                        }

                    } else {  # left char must be a word
                        if (defined $left_is_word && $left_is_word != -1) {
                            if ($left_is_word == 1) {
                                $src .= "asserts |= " . (1 << $idx) . ";\n";
                            } else {
                                # do nothing, since it's "asserts |= 0;".
                            }

                        } else {
                            if ($min_len >= 1) {
                                $src .= $indent . 'asserts |= is_word(s[i - 2]) << '
                                       . "$idx;\n";
                            } else {
                                $src .= $indent . 'asserts |= (i >= 2 ? is_word(s[i - 2]) : 0) << '
                                       . "$idx;\n";
                            }
                        }
                    }

                } else {
                    if (defined $left_is_word && $left_is_word != -1) {
                        if ($left_is_word == 1) {  # right char must not be a word
                            $src .= $indent . 'asserts |= !is_word(c) << ' . "$idx;\n";
                        } else {  # right char must be a word
                            $src .= $indent . 'asserts |= is_word(c) << ' . "$idx;\n";
                        }

                    } else {
                        if ($min_len >= 1) {
                            $src .= $indent . 'asserts |= is_word_boundary(s[i - 2], c) << '
                                   . "$idx;\n";
                        } else {
                            $src .= $indent . 'asserts |= is_word_boundary(i >= 2 ? s[i - 2] : -1, c) << '
                                   . "$idx;\n";
                        }
                    }
                }
            } elsif ($assert eq '\B') {
                if ($min_len >= 1) {
                    $src .= $indent . 'asserts |= !is_word_boundary(s[i - 2], c) << '
                           . "$idx;\n";
                } else {
                    $src .= $indent . 'asserts |= !is_word_boundary(i >= 2 ? s[i - 2] : -1, c) << '
                           . "$idx;\n";
                }
            } elsif ($assert eq '\A') {
                $src .= $indent . 'asserts |= (i == 1) << '
                                   . "$idx;\n";
            } elsif ($assert eq '\z') {
                $src .= $indent . 'asserts |= (c == -1) << ' . "$idx;\n";
            } else {
                die "TODO";
            }
            $src .= $indent . qq{fprintf(stderr, "assertion $assert test result: %d, idx = $idx, i = %d, c = %d\\n", asserts, i, c);\n}
                if $debug;
        }

        my $assert_edges = $target->{edges};

        #warn "assert edges: $assert_edges\n";

        #warn "$edge: ", $target->{max_assert_settings}, " vs ", scalar @$assert_edges;
        my $use_default = (@$assert_edges == $target->{max_assert_settings} + 1);
        for my $subedge (@$assert_edges) {
            my $assert_settings = $subedge->{assert_settings};
            #die unless ref $assert_settings;
            my $target = $subedge->{target};
            my $indent2;
            if ($use_default && $subedge eq $assert_edges->[-1]) {
                $src .= $indent . "{ /* asserts == $assert_settings */\n";
            } else {
                $src .= $indent . "if (asserts == $assert_settings) {\n";
            }
            $indent2 = $indent . (" " x 4);
            if ($target->{accept}) {
                $to_accept = 1;
            }
            $src .= gen_capture_handler_c_code($subedge, $target->{accept}, $indent2, $nvec);
            my $to = $target->{idx};
            if (!$to_accept) {
                $src .= $indent2 . "goto st$to;\n";
            }
            $src .= $indent . "}\n";
        }

    } else {
        # normal DFA edge w/o assertions

        $src .= gen_capture_handler_c_code($edge, $to_accept, $indent, $nvec);

        my $to = $target->{idx};
        if (!$to_accept && !$edge->{memchr}) {
            if (!defined $to) {
                warn Dumper($edge);
                croak Dumper($target);
            }
            $src .= $indent . "goto st$to;\n";
        }
    }

    if (@cond) {
        if (!$default_br && !$use_switch) {
            $indent_idx--;
            $src .= $indents[$indent_idx] . "}\n";
        } elsif ($use_switch) {
            $src .= $indents[$indent_idx] . "break;\n";
            $src .= $indents[$indent_idx] . "}\n";
            $indent_idx--;
            if (!$new_use_switch) {
                $src .= $indents[$indent_idx] . "}\n";
            }
        }
    }

    return $src, $to_accept, $new_use_switch;
}

sub gen_capture_handler_c_code ($$$$) {
    my ($edge, $to_accept, $indent, $nvec) = @_;

    my $src = '';
    my $target = $edge->{target};
    my $mappings = $edge->{capture_mappings};
    my $target_actions = $edge->{nfa_edges};

    my (%to_save_rows, %overwritten, @stores, %to_be_stored);
    for my $mapping (@$mappings) {
        my ($from_row, $to_row) = @$mapping;

        my $nfa_edge = $target_actions->[$to_row];
        for my $pc (@$nfa_edge) {
            my $bc = $bytecodes[$pc];
            my $bcname = opcode($bc);
            if ($bcname eq 'save') {
                my $id = $bc->[1];
                if ($to_accept) {
                    push @stores, "matched_$id = i - 1;";
                } else {
                    push @stores, "caps${to_row}_$id = i - 1;";
                    $to_be_stored{"$to_row-$id"} = 1;
                }
            } elsif ($bcname eq 'assert') {
                #warn "TODO: assertions";
            }
        }

        if (!$to_accept && $from_row != $to_row) {
            if ($overwritten{$from_row}) {
                $to_save_rows{$from_row} = 1;
            }
            if (!$to_be_stored{$to_row}) {
                $overwritten{$to_row} = 1;
            }
        }
    }

    %overwritten = ();

    my @transfers;
    for my $mapping (@$mappings) {
        my ($from_row, $to_row) = @$mapping;

        if ($to_accept) {
            my $t = $indent . "/* transfer caps from row $from_row to matched */\n";
            for (my $i = 0; $i < $nvec; $i++) {
                $t .= $indent . "matched_$i = caps${from_row}_$i;\n";
            }
            push @transfers, $t;

        } elsif ($from_row != $to_row) {
            my $t = $indent . "/* transfer caps from row $from_row to row $to_row */\n";
            for (my $i = 0; $i < $nvec; $i++) {
                if (!$to_be_stored{"$to_row-$i"}) {
                    my $to_var = "caps${to_row}_$i";
                    if ($to_save_rows{$to_row}) {
                        $t .= $indent . "tmp${to_row}_$i = $to_var;\n";
                    }
                    my $from_var;
                    if ($overwritten{$from_row} && !$to_be_stored{"$from_row-$i"}) {
                        $from_var = "tmp${from_row}_$i";
                    } else {
                        $from_var = "caps${from_row}_$i";
                    }
                    $t .= $indent . "$to_var = $from_var;\n";
                }
            }
            $overwritten{$to_row} = 1;
            push @transfers, $t;
        }

    }

    if (@transfers) {
        if (%to_save_rows) {
            $src .= $indent . "{\n";
            my @tmp;
            for my $row (sort keys %to_save_rows) {
                for (my $i = 0; $i < $nvec; $i++) {
                    if (!$to_be_stored{"$row-$i"}) {
                        push @tmp, "tmp${row}_$i";
                    }
                }
            }
            $src .= $indent . "int " .  join(", ", @tmp) . ";\n";
        }
        $src .= join "", @transfers;
        if (%to_save_rows) {
            $src .= $indent . "}\n";
        }
    }

    if (@stores) {
        $src .= $indent . join("\n$indent", @stores) . "\n";
    }

    return $src;
}

sub usage ($) {
    my $rc = shift;
    my $msg = <<"_EOC_";
Usage:
    re.pl [options] <regex> <string>
    re.pl [options] --stdin <regex> < input-file

Options:
    --cc=NAME       specify the name of the C compiler used to compile
                    the generated C code for the regex. a full path
                    can be accepted too. default to "cc".

    --debug=LEVEL   specify the debug output level; valid values are
                    0, 1, and 2.

    -g              perform global search (similar to Perl's /g mode).

    --help          show this usage.

    --out=FILE      specify the output executable file generated by the
                    C compiler.

    --repeat=N      repeat the operations for N times (default to 3) and pick
                    the best result. only effective when --timer is specified.

    --timer         insert timer code for the match routine in the compiled
                    program.

    --stdin         accept the subject string (to be matched) from the
                    stdin device instead of the second command-line
                    argument.
_EOC_
    if ($rc) {
        warn $msg;
        exit $rc;
    }
    print $msg;
    exit 0;
}

sub dump_code ($) {
    my ($code) = @_;
    my $ln = 1;
    (my $str = $code) =~ s/^/sprintf("%3s ", $ln++)/gem;
    return $str;
}

sub count_chars_in_ranges ($) {
    my ($ranges) = @_;
    return 0 unless defined $ranges;
    my $count = 0;
    my $n = @$ranges;
    for (my $i = 0; $i < $n; $i += 2) {
        my ($a, $b) = ($ranges->[$i], $ranges->[$i + 1]);
        $count += $b - $a + 1;
    }
    return $count;
}

sub analyze_dfa ($) {
    my ($dfa) = @_;

    my $dfa_nodes = $dfa->{nodes};

    # compute min/max length of input string consumed for each DFA node.
    for my $node (@$dfa_nodes) {
        if ($node->{start}) {
            $node->{min_len} = 0;
        }
        #$node->{max_len} = 0;
    }

    my $changes;
    do {{
        $changes = 0;
        for my $node (@$dfa_nodes) {
            #warn "=== checking node $node->{idx}";
            my $min = $node->{min_len};
            #my $max = $node->{max_len};
            my $edges = $node->{edges};
            my @all_edges = @$edges;
            for (my $i = 0; $i < @all_edges; $i++) {
                my $edge = $all_edges[$i];
                my $target = $edge->{target};
                if (defined $edge->{shadowing}) {
                    push @all_edges, $edge->{shadowing};
                }
                #warn "--- checking target $target->{idx}";
                my $min2 = $target->{min_len};
                #my $max2 = $target->{max_len};
                my $delta;
                if (defined $edge->{char_ranges}) {
                    # must consume a char
                    $delta = 1;
                } else {
                    $delta = 0;
                }

                if (defined $min) {
                    if (!defined $min2 || $min + $delta < $min2) {
                        $target->{min_len} = $min + $delta;
                        #warn "set node $target->{idx}'s min_len to ", $target->{min_len};
                        $changes++;
                    } else {
                        #warn "nothing to be done for node $target->{idx}";
                    }
                } else {
                    #warn "nothing to be done for node $target->{idx}";
                }

=begin comment

                if ($target eq $node || !defined $max) {
                    if (defined $max2) {
                        #warn "set node $target->{idx}'s max_len to Inf";
                        undef $target->{max_len};
                        $changes++;
                    } else {
                        #warn "nothing to be done for node $target->{idx}";
                    }

                } else {
                    if (defined $max2 && $max + $delta > $max2) {
                        $target->{max_len} = $max + $delta;
                        #warn "set node $target->{idx}'s max_len to ", $target->{max_len};
                        $changes++;
                    } else {
                        #warn "nothing to be done for node $target->{idx}";
                    }
                }

=end comment

=cut
            }  # for
        }  # for
        #warn "iteration done: $changes";
    }} while ($changes > 0);

    $changes = 0;
    for my $node (@$dfa_nodes) {
        if (!defined $node->{min_len}) {
            # remove unreachable nodes
            $changes++;
            undef $node;
        }
    }

    if ($changes > 0) {
        #warn "removed $changes unreacheable nodes.\n";
        @$dfa_nodes = grep { defined } @$dfa_nodes;
    }
}
