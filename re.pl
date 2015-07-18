#!/usr/bin/env perl

use strict;
use warnings;

use IPC::Run3;
use Data::Dumper;
use GraphViz;
use Time::HiRes qw( time );
use List::MoreUtils qw( uniq firstidx );
use List::Util qw( first max );
use Carp qw( croak carp );
use Getopt::Long qw( GetOptions );
use File::Temp qw( tempfile );
use POSIX qw( tmpnam );

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
sub gen_c_for_dfa_edge ($$$$);
sub dump_code ($);

my $DEBUG = 0;

my $cc = "cc";

GetOptions("help|h",        \(my $help),
           "cc=s",          \$cc,
           "stdin",         \(my $stdin))
   or die usage(1);

if ($help) {
    usage(0);
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

my @cmd = ("./sregex-cli", $re);
run3 \@cmd, undef, \(my $res), \(my $err);

print "$res";
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

#my $begin = time;
my $nfa = gen_nfa();
#my $elapsed = time - $begin;
#warn "NFA generated ($elapsed sec).\n";
#warn Dumper($nfa);
draw_nfa($nfa) if $DEBUG;

#$begin = time;
my $dfa = gen_dfa($nfa);
#$elapsed = time - $begin;
#warn "DFA generated ($elapsed sec).\n";

#warn Dumper($dfa);
draw_dfa($dfa) if $DEBUG;

#exit;
my $c = gen_c_from_dfa($dfa);
warn dump_code($c) if $DEBUG == 2;
#$begin = time;
{
    my ($fh, $fname) = tempfile(SUFFIX => '.c', UNLINK => 1);
    #warn $fname;
    print $fh $c;
    close $fh;
    my $exefile = tmpnam();
    #system("cc -o $exefile -Wall -Wno-unused-label -Wno-unused-variable -Wno-unused-but-set-variable -Werror -O0 $fname") == 0
    my $extra_ccopt = "";
    if ($DEBUG) {
        $extra_ccopt = "-Wall -Wno-unused-label -Wno-unused-variable -Wno-unused-but-set-variable -Werror";
    }
    system("$cc -o $exefile $extra_ccopt $fname") == 0 or die "$!\n";
    my @cmd = ($exefile);

    #my $begin = time;
    #$elapsed = time - $begin;
    #warn "Perl code execution done ($elapsed sec).\n";

    run3 \@cmd, \$subject, \(my $out), \(my $err);

    my $rc = $?;

    if ($err) {
        print STDERR $err;
    }

    unlink $exefile or die $!;

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

        # fix the path mappings in the DFA edges

        for my $dfa_edge (@$dfa_edges) {
            calc_capture_mapping($dfa_node, $dfa_edge);
            my $shadowing = $dfa_edge->{shadowing};
            if (defined $shadowing) {
                calc_capture_mapping($dfa_node, $shadowing);
            }
        }

        #warn "DFA node ", gen_dfa_node_label($dfa_node), "\n";
        $i++;
    }

    return {
        nodes => \@dfa_nodes,
        nvec => $nfa->{nvec},
    };
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
    if ($node->{start}) {
        return "0";
    }
    my @lines = (join ",", @{ $node->{states} });
    push @lines, "[" . $node->{idx} . "]";
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
            croak Dumper($range);
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

    my $src = <<'_EOC_';
#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>


#define u_char  unsigned char


enum {
    NO_MATCH = 0,
    MATCHED  = 1,
    BUFSIZE = 4096
};


static inline int
is_word_boundary(int a, int b)
{
    a = (a != -1 && (isalnum(a) || a == '_'));
    b = (b != -1 && (isalnum(b) || b == '_'));
    return (a ^ b);
}


static int
match(const u_char *s, size_t len, int *ovec)
{
    int c;
    int i = 0;
_EOC_

    my $nvec = $dfa->{nvec};
    #die "nvec: $nvec";

    {
        for (my $i = 0; $i < $nvec; $i++) {
            $src .= "    int matched_$i = -1;\n";
        }
    }

    my $dfa_nodes = $dfa->{nodes};

    my $level = 1;

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
        my $idx = $node->{idx};

        if (defined $node->{assert_info} || $node->{accept}) {
            next;
        }

        my $label = gen_dfa_node_label($node);
        $label =~ s/\\n/ /g;

        if ($idx != 0) {
            $src .= "\nst$idx: {  /* DFA node $label */\n";
        } else {
            $src .= "\n    {  /* DFA node $label */\n";
        }

        $src .= qq{    fprintf(stderr, "entering state $label\\n");\n} if $DEBUG;
        $src .= "    c = i < len ? s[i++] : (i++, -1);\n";
        $src .= qq{    fprintf(stderr, "reading new char \\"%d\\"\\n", c);\n} if $DEBUG;

        my $first_time = 1;
        my $edges = $node->{edges};
        my $used_error;
        my $seen_accept;
        for my $edge (@$edges) {
            my ($new_src, $to_accept) = gen_c_for_dfa_edge($idx, $edge, $level, $nvec);

            if ($to_accept) {
                $seen_accept = 1;
            }

            if ($first_time) {
                undef $first_time;
                if (!$seen_accept) {
                    $used_error = 1;
                    $src .= <<_EOC_;
    if (c == -1) {
        goto st${idx}_error;
    }
_EOC_
                }
            }

            $src .= $new_src;

            if ($to_accept) {
                $src .= "    if (c != -1) {\n";
                $level++;
            }
        }

        if ($seen_accept) {
            $src .= "    }\n";
            $level--;
        }

        $src .= "    }  /* end state */\n\n";

        if ($used_error) {
            $src .= "st${idx}_error:\n";
        }

        for (my $i = 0; $i < $nvec; $i++) {
            $src .= "    ovec[$i] = matched_$i;\n";
        }

        $src .= "    return MATCHED;  /* fallback */\n";
    }

    $src .= <<"_EOC_";
}


int
main(void)
{
    int          ovec[$nvec];
    char        *p, *buf;
    size_t       len, bufsize, rest;

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
        int rc;

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
        p += rc;

        if (feof(stdin)) {
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
    } while (1);

    if ($DEBUG == 2) {
        fprintf(stderr, "input string: %.*s\\n", (int) len, buf);
    }

    {
        int rc;
        rc = match((u_char *) buf, len, ovec);
        if (rc == NO_MATCH) {
            printf("no match.\\n");
            return 0;
        }
    }

    /* matched */

    printf("matched:");
    {
        int i;

        for (i = 0; i < $nvec; i += 2) {
            printf(" (%d, %d)", ovec[i], ovec[i + 1]);
        }
    }
    printf("\\n");

    return 0;
}
_EOC_
    return $src;
}

sub gen_c_for_dfa_edge ($$$$) {
    my ($from_node_idx, $edge, $level, $nvec) = @_;

    my $src = '';
    my @indents = (" " x (4 * $level), " " x (4 * ($level + 1)));
    my $indent_idx = 0;

    my $ranges = $edge->{char_ranges};
    my $target = $edge->{target};
    my $to_accept = $edge->{to_accept};

    #warn "to accept: $to_accept";

    my @cond;
    if (defined $ranges && !$edge->{shadowed}) {
        for (my $i = 0; $i < @$ranges; $i += 2) {
            my ($a, $b) = ($ranges->[$i], $ranges->[$i + 1]);
            if ($a == $b) {
                push @cond, "c == $a";
            } else {
                push @cond, "c >= $a && c <= $b";
            }
        }
    }

    if (@cond) {
        my $cond;
        if (@cond == 1) {
            $cond = $cond[0];
        } else {
            $cond = join " || ", map { "($_)" } @cond;
        }
        $src .= $indents[$indent_idx] . "if ($cond) {\n";
        $indent_idx++;

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
                my ($inner, $to_accept) = gen_c_for_dfa_edge($from_node_idx, $shadowing,
                                                             $level + 2, $nvec);
                if (defined $inner) {
                    $src .= $inner;
                }
                die if $to_accept;
                $src .= $indent . "}\n";
            }
        }
    }

    my $assert_info = $target->{assert_info};
    my $indent = $indents[$indent_idx];
    if (defined $assert_info) {
        my $asserts = $assert_info->{asserts};
        $src .= $indent . "int asserts = 0;\n";
        for my $assert (sort keys %$asserts) {
            my $idx = $asserts->{$assert};
            if ($assert eq '^') {
                $src .= $indent . 'asserts |= (i == 1 || (i >= 2 && s[i - 2] == 10)) << '
                                   . "$idx;\n";
            } elsif ($assert eq '$') {
                $src .= $indent . 'asserts |= (c == -1 || c == 10) << ' . "$idx;\n";
            } elsif ($assert eq '\b') {
                $src .= $indent . 'asserts |= is_word_boundary(i >= 2 ? s[i - 2] : -1, c) << '
                                   . "$idx;\n";
            } elsif ($assert eq '\B') {
                $src .= $indent . 'asserts |= !is_word_boundary(i >= 2 ? s[i - 2] : -1, c) << '
                                   . "$idx;\n";
            } elsif ($assert eq '\A') {
                $src .= $indent . 'asserts |= (i == 1) << '
                                   . "$idx;\n";
            } elsif ($assert eq '\z') {
                $src .= $indent . 'asserts |= (c == -1) << ' . "$idx;\n";
            } else {
                die "TODO";
            }
            $src .= $indent . qq{fprintf(stderr, "assertion $assert test result: %d, idx = $idx, i = %d, c = %d\\n", asserts, i, c);\n}
                if $DEBUG;
        }

        my $assert_edges = $target->{edges};

        #warn "assert edges: $assert_edges\n";

        for my $subedge (@$assert_edges) {
            my $assert_settings = $subedge->{assert_settings};
            #die unless ref $assert_settings;
            my $target = $subedge->{target};
            $src .= $indent . "if (asserts == $assert_settings) {\n";
            my $indent2 = $indent . (" " x 4);
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
        if (!$to_accept) {
            if (!defined $to) {
                warn Dumper($edge);
                croak Dumper($target);
            }
            $src .= $indent . "goto st$to;\n";
        }
    }

    if (@cond) {
        $indent_idx--;
        $src .= $indents[$indent_idx] . "}\n";
    }

    return $src, $to_accept;
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
    re.pl <regex> <string>
    re.pl --stdin <regex> < input-file
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
