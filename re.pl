#!/usr/bin/env perl

# This is a quick prototype in Perl for the new DFA backend
# for the sregex engine. This prototype serves to verify the
# algorithms and estimate the ultimate performance.
#
# This prototype is currently a compiler that compiles reges
# patterns down to standalone pure C programs that can do
# the matching on input data files. So this prototype invokes
# external C compiler toolchain (like gcc/clang/tcc) to
# compile the resulting C programs.
#
# To run this script, you need to build sregex by the following
# command:
#
#   make
#
# Also, you need to install those Perl CPAN modules this script
# depends on via the following command:
#
#   cpan GraphViz IPC::Run3 List::MoreUtils
#
# And you need to have the C compiler toolchain in your system.
#
# Usge examples:
#
#   $ ./re.pl 'a(b)|a' 'caba'
#   SRegex DFA proto match (1, 3) (2, 3)
#
#   # generate a standalone binary program "foo" and its
#   # corresponding C source file "foo.c":
#   $ ./re.pl -o foo 'a|b' 'a'
#
#   # the following command generates some debug outputs
#   # as well as PNG images ./nfa.png and ./dfa-partial.png,
#   # for the NFA and DFA graphs, respectively.
#   $ ./re.pl --debug=1 'ab|a' 'cab'
#
#   # even more verbose outputs.
#   $ ./re.pl --debug=2 'a+' 'a'
#
# Under the hood, this program uses my own DFA-based algorithm
# that supports general sub-match capturing as well as
# all other goodies sregex already supports, including 0-width
# assertions. The essential idea is "determinizing" Thompson's
# NFA simulation algorithms with the Rob Pike extension that
# adds sub-match capturing support.
#
# Currently all the regex syntax supported by the mainline
# sregex is supported by this prototype. The whole existing
# sregex test suite is passed completely by this toy.
#
# Eventually this toy will be ported over to pure C and a
# Just-In-Compiler will be added so as to get rid of
# the external C compiler toolchain if we wish. We may still
# keep # a static C code emitter in the final pure C
# implementation of this prototype though.
#
# Copyright (C) 2015 Yichun Zhang (agentzh).
#
# This program can be redistributed under the same terms as
# the sregex library itself.

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

sub rewrite_repetitions ($);
sub as_in_range_bytecode ($$);
sub add_nfa_edges ($$$$);
sub gen_nfa_edge_label ($);
sub escape_char ($);
sub escape_range_char ($);
sub gen_nfa ();
sub draw_nfa ($);
sub bc_is_nfa_node ($);
sub opcode ($);
sub gen_dfa_edges ($$$$$$);
sub gen_dfa ($);
sub dedup_nfa_edges ($);
sub reorder_nfa_edges ($$);
sub draw_dfa ($);
sub draw_partial_dfa ($$);
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
sub gen_edge_action_c_code ($$);
sub gen_c_from_dfa_edge ($$$$$);
sub gen_c_from_dfa_node ($$);
sub gen_src_cap_var ($$$);
sub gen_dst_cap_var ($$$);
sub dump_code ($);
sub count_chars_and_holes_in_ranges ($);
sub analyze_dfa ($);
sub dump_bytecode ($);
sub pc2bc ($);

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

if (!defined $timer) {
    $timer = 0;
}

if (!$repeat) {
    if ($timer) {
        $repeat = 5;
    } else {
        $repeat = 1;
    }
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

my %counting_state_twins;
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

if (1) {
    my $n = rewrite_repetitions(\@bytecodes);
    if ($n > 0 && $debug) {
        print "Rewrote $n repetitions. New bytecode dump:\n";
        print dump_bytecode(\@bytecodes);
    }
}

#warn Dumper \@bytecodes;

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

my %action_prio = (
    #delcnt => 0,
    addcnt => 1,
    inccnt => 2,
);

my %action_labels = (
    addcnt => '+cnt',
    #delcnt => '-cnt',
    inccnt => 'cnt++',
    clrcnt => 'clrcnt',
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

my $edge_attr =
{
    color => 'red',
};

my %nfa_paths;
my %pc2assert;
my $used_asserts;
my %counter_sets;

#my $begin = time;
my $nfa = gen_nfa();
#my $elapsed = time - $begin;
#warn "NFA generated ($elapsed sec).\n";
#warn Dumper($nfa);
warn scalar @{ $nfa->{nodes} }, " NFA nodes found.\n" if $debug;
draw_nfa($nfa) if $debug;

#$begin = time;
my $dfa = gen_dfa($nfa);
#$elapsed = time - $begin;
#warn "DFA generated ($elapsed sec).\n";
analyze_dfa($dfa);

warn scalar @{ $dfa->{nodes} }, " DFA nodes found.\n" if $debug;

#warn Dumper($dfa);
draw_dfa($dfa) if $debug > 1;

#exit;
my $c = gen_c_from_dfa($dfa);
warn dump_code($c) if $debug > 2;
#$begin = time;
{
    my ($fh, $fname);
    my $exe_tmp;
    if (!defined $exefile) {
        ($fh, $fname) = tempfile(SUFFIX => '.c', UNLINK => 1);
        $exefile = tmpnam();
        $exe_tmp = 1;
    } else {
        unlink $exefile if -f $exefile;
        $fname = $exefile . ".c";
        open $fh, ">$fname" or die "cannot open $fname for writing: $!\n";
    }

    #warn $fname;
    print $fh $c;
    close $fh;

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

    if ($debug && $err) {
        my @route;
        open my $in, "<", \$err or die $!;
        while (<$in>) {
            #warn "!! $_";
            next if /^\s*$/;
            if (/^\* entering (?:accept )?state \{[^}]+\} (\d+)/) {
                my $state = $1;
                push @route, $state;
            } elsif (/^hit assertion DFA node (\d+)/) {
                my $state = $1;
                push @route, $state;
            }
        }
        close $in;
        draw_partial_dfa($dfa, \@route);
    }

    print $out;
}

sub gen_nfa () {
    my @nodes;
    my $max_cap = 0;
    my $idx = 0;
    for my $bc (@bytecodes) {
        next unless defined $bc;
        my $opcode = opcode($bc);
        if ($opcode eq 'assert') {
            $used_asserts = 1;
            if (!exists $pc2assert{$idx}) {
                my $assert = $bc->[1];
                if ($assert eq 'cnt') {
                    my @v = @$bc;
                    shift @v;
                    $assert = join " ", @v;
                }
                $pc2assert{$idx} = $assert;
                #warn "new assert $assert";
                $found = 1;
            }
        } elsif ($opcode eq 'save') {
            my $n = $bc->[1];
            if ($n > $max_cap) {
                $max_cap = $n;
            }
        }

        $opcode = bc_is_nfa_node($bc);
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

    my @ext_nodes;
    for my $node (@nodes) {
        my %visited;
        my $idx = $node->{idx};
        next if $node->{accept};
        add_nfa_edges($node, $idx == 0 ? 0 : $idx + 1, \%visited, undef);

        if (defined $counter_sets{$idx}) {
            # create a mirror for counting NFA states with a reversed NFA
            # edge order.
            # Note: here we assume there's no extra NFA edges looping
            # through the counting NFA state itself. this is currently
            # guarenteed by an artificial sentinel NFA node right after
            # the counting state.
            my @edges = @{ $node->{edges} };
            #warn "counting node edges: ", Dumper(\@edges);
            die if @edges != 2;
            my $last_edge = [ @{ $edges[-1] } ];
            my $bc = pc2bc($last_edge->[0]);
            #warn Dumper($bc);
            die if $last_edge->[-1] != $idx || !ref $bc || $bc->[0] ne 'assert' || $bc->[2] != $idx;
            $last_edge->[-1] = -$idx;
            $edges[-1] = $last_edge;
            @edges = reverse @edges;
            my $twin_node = {
                idx => -$idx,
                edges => \@edges,
            };
            #warn "counting node edges 2: ", Dumper($twin_node->{edges});
            push @ext_nodes, $twin_node;
            $node->{twin} = $twin_node;
        }
    }

    if (@ext_nodes) {
        push @nodes, @ext_nodes;
    }

    return {
        nodes => \@nodes,
        nvec => $max_cap + 1,
    }
}

sub draw_nfa ($) {
    my ($nfa) = @_;

    my $nfa_nodes = $nfa->{nodes};

    my $big;
    if (@$nfa_nodes >= 20) {
        $node_attr->{height} = 0.1;
        $edge_attr->{arrowsize} = 0.5;
        $big = 1;
    } else {
        undef $node_attr->{height};
        undef $edge_attr->{arrowsize};
    }

    my $graph = GraphViz->new(
        layout => $big ? 'twopi' : 'neato',
        ratio => 'auto',
        node => $node_attr,
        edge => $edge_attr,
    );

    #$graph->as_dot("nfa.dot");
    for my $node (@$nfa_nodes) {
        my $idx = $node->{idx};
        #next if $idx < 0;
        my $style;
        if (defined $counter_sets{$idx}) {
            $style = "filled,dashed";
        }
        $graph->add_node("n$idx", $node->{start} ? (color => 'orange') : (),
                         $node->{accept} ? (shape => 'doublecircle') : (),
                         label => $big ? '' : $idx || " $idx",
                         defined $style ? (style => $style) : ());
    }
    for my $node (@$nfa_nodes) {
        my $from_idx = $node->{idx};
        #next if $from_idx < 0;
        #if ($from_idx == 15) {
            #warn "Draw NFA eges for NFA node $from_idx: ", Dumper($node->{edges});
            #}
        my $e_idx = 0;
        for my $e (@{ $node->{edges} }) {
            my ($label, $style) = gen_nfa_edge_label($e);
            my $to_idx = $e->[-1];
            my $color = $edge_colors[$e_idx] || 'black';
            $graph->add_edge("n$from_idx" => "n$to_idx", label => $label,
                             color => $color, len => 1.6,
                             defined $style ? (style => $style) : ());
            $e_idx++;
        }
    }
    $graph->as_png("nfa.png");
}

sub add_nfa_edges ($$$$) {
    my ($from_node, $idx, $visited, $to_nodes) = @_;

    #warn "add edges: $from_node->{idx} => $idx";
    my $bc = pc2bc($idx);
    return unless defined $bc;

    my $opcode = opcode($bc);

    if ($opcode eq 'nop') {
        for ($idx++; $idx < @bytecodes; $idx++) {
            $bc = pc2bc($idx);
            if (!ref $bc && $bc eq 'nop') {
                next;
            }
            # found the boundary.
            $opcode = opcode($bc);
            last;
        }
        if ($opcode eq 'nop') {
            return;
        }
        #warn "skipped NOP and reached bytecode $idx: $opcode";
    }

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
        # we must fork the visited hash table to allow parallel edges with different assertions.
        my %visited_fork = %$visited;
        add_nfa_edges($from_node, $x, \%visited_fork, $to_nodes);
        #add_nfa_edges($from_node, $x, $visited, $to_nodes);
        local @_ = ($from_node, $y, $visited, $forked);
        goto \&add_nfa_edges;
    }

    if ($opcode eq 'save' or $opcode eq 'assert' or $opcode =~ /^(?:add|inc|del)cnt$/) {
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

sub bc_is_nfa_node ($) {
    my ($bc) = @_;
    my $opcode = opcode($bc);
    if ($opcode =~ /^(?:char|notin|in|any|match)$/) {
        return $opcode;
    }
    undef;
}

sub gen_nfa_edge_label ($) {
    my ($e) = @_;
    my $total_consuming;
    my @styles;
    my @labels;
    for my $idx (@$e) {
        my $bc = pc2bc($idx);
        my $opcode = opcode($bc);
        #warn "opcode: $opcode\n";
        my $info = $cached_labels{$bc};
        my ($label, $consuming, $style);
        if (defined $info) {
            ($label, $consuming, $style) = @$info;
        } else {
            my $v = ref $bc ? $bc->[1] : undef;
            if ($opcode eq 'assert') {
                if ($v eq 'cnt') {
                    my $op = $bc->[-2];
                    my $n = $bc->[-1];
                    if ($op eq 'n ne') {
                        $op = '≠';
                    } else {
                        $op = '=';
                    }
                    $label = "cnt$op$n";

                } else {
                    $label = $v;
                }
            } elsif ($opcode eq 'any') {
                $label = '*';
                $consuming = 1;
            } elsif ($opcode eq 'char') {
                $label = "'" . escape_char($v) . "'";
                $consuming = 1;
            } elsif ($opcode eq 'in') {
                my @args = @$bc;
                shift @args;
                $label = escape_range(\@args, 0);
                $consuming = 1;
            } elsif ($opcode eq 'notin') {
                my @args = @$bc;
                shift @args;
                $label = escape_range(\@args, 1);
                $consuming = 1;
            } elsif ($opcode eq 'save') {
                my $i = int($v / 2);
                my $sym = $v % 2 == 0 ? '(' : ')';
                $label = "$sym$i";
            } elsif ($opcode eq 'match') {
                #$label = "ε";
            } elsif ($opcode eq 'addcnt') {
                $label = "+cnt";
            #} elsif ($opcode eq 'delcnt') {
                #$label = "-cnt";
            } elsif ($opcode eq 'inccnt') {
                $label ="cnt++";
            } else {
                croak "unknown opcode: $opcode";
            }

            $cached_labels{$bc} = [$label, $consuming, $style];
        }
        if ($consuming) {
            $total_consuming = 1;
        }
        if (defined $style) {
            push @styles, $style;
        }
        #$label =~ s/\\/\\\\/g;
        if (defined $label) {
            push @labels, $label;
        }
    }
    #warn "consuming: $consuming, labels: @labels";
    if ($total_consuming && @labels > 1) {
        my $input = pop @labels;
        return "$input| " . join(",", @labels), join ",", @styles;
    }
    return join(",", @labels), join ",", @styles;
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

        #warn "processing node $dfa_node->{idx}";

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
                #my $idx = $nfa_node->{idx};
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
                my $target = $dfa_edge->{target};
                #warn("compute incoming edges for node $target->{idx} (from $dfa_node->{idx})");
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
        my $left_is_ln_start; # ditto
        for my $dfa_edge (@$incoming) {
            my $ranges = $dfa_edge->{char_ranges};
            if (defined $ranges) {
                for (my $i = 0; $i < @$ranges; $i += 2) {
                    my ($a, $b) = ($ranges->[$i], $ranges->[$i + 1]);
                    my $s;
                    if (!defined $left_is_word || $left_is_word != -1) {
                        $s = join "", map { chr } $a .. $b;
                        if ($s =~ /^\w+$/) {
                            $left_is_word = !defined $left_is_word || $left_is_word == 1 ? 1 : -1;
                        } elsif ($s =~ /^\W+$/) {
                            $left_is_word = !defined $left_is_word || $left_is_word == 0 ? 0 : -1;
                        } else {
                            $left_is_word = -1;
                        }
                    }
                    if (!defined $left_is_ln_start || $left_is_ln_start != -1) {
                        $s //= join "", map { chr } $a .. $b;
                        if ($s =~ /^\n+$/s) {
                            #warn "HIT";
                            $left_is_ln_start = !defined $left_is_ln_start || $left_is_ln_start == 1 ? 1 : -1;
                        } elsif ($s !~ /\n/s) {
                            #warn "HIT \\N+: ", Dumper($s);
                            $left_is_ln_start = !defined $left_is_ln_start || $left_is_ln_start == 0 ? 0 : -1;
                        } else {
                            $left_is_ln_start = -1;
                        }
                    }
                }
            }
        }

        if (defined $left_is_word) {
            $dfa_node->{left_is_word} = $left_is_word;
            #if ($left_is_word != -1) {
                #warn "Found node $dfa_node->{idx} whose left char is always a ",
                #$left_is_word ? "" : "non", "word";
            #}
        }

        if (defined $left_is_ln_start) {
            $dfa_node->{left_is_ln_start} = $left_is_ln_start;
            #if ($left_is_ln_start != -1) {
                #warn "Found node $dfa_node->{idx} whose left char is always a ",
                #$left_is_ln_start ?  "" : "non", "line start";
            #}
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
    #warn "src $from_node->{idx} {", join(",", @$src_states),
        #"} => dst $dfa_edge->{target}{idx} ",
    #gen_dfa_node_label($dfa_edge->{target}), "\n";
    for my $raw_src_state (@$src_states) {
        my $src_state = abs $raw_src_state;
        my $to_row_cnt = 0;
        my %seen_dst_state;
        for my $nfa_edge (@$nfa_edges) {
            my $to_pc = abs $nfa_edge->[0]; # first NFA node in the NFA edge, not the last one
            my $dst_state = abs $nfa_edge->[-1];
            my $to_row = $seen_dst_state{$dst_state};
            if (!defined $to_row) {
                $seen_dst_state{$dst_state} = 1;
                $to_row = $to_row_cnt;
            } else {
                $to_row_cnt--;
            }
            my $key = "$src_state-$to_pc";
            if (!$assigned{$to_row} && $nfa_paths{$key}) {
                my $src_counting = $counter_sets{$src_state};
                if (defined $src_counting) {
                    my $dst_counting = $counter_sets{$dst_state}; # here we must use the last one
                    if (defined $dst_counting && $dst_counting == $src_counting) {
                        # skip mapping counter state to the same counter state
                        # since the mapping is implicit by keeping the same
                        # counter_ovec_set_xxx row through such transitions.
                        # more importantly, we prevent this useless edge from
                        # hiding subsequent edges with "addcnt" actions which
                        # does real jobs.
                        #warn "@$bc";
                        #warn "  skipped mapping: $from_row => $to_row\n";
                        next;
                        #warn "  mapping: $from_row => $to_row\n";
                    }
                }
                #warn "  mapping: $from_row => $to_row\n";
                push @mappings, [$from_row, $to_row, $src_state, $dst_state];
                $assigned{$to_row} = 1;
            }
        } continue {
            $to_row_cnt++;
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
    my $bad_assert_settings = $assert_info->{bad_assert_settings};
    # split the DFA edge according to assertions' on/off combinations
    my @dfa_edges;
    my $max_encoding = 2 ** $uniq_assert_cnt - 1;
    for (my $comb_encoding = 0; $comb_encoding <= $max_encoding; $comb_encoding++) {
        if ($bad_assert_settings->{$comb_encoding}) {
            #warn "HIT $comb_encoding ($from_node->{idx})";
            next;
        }
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
            #warn("not possible $comb_encoding ($from_node->{idx})");
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
        $dfa_edge = resolve_dfa_edge($from_node, $dfa_edge, undef, \%targets,
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
            #warn "in shadow: @$nfa_edge";
            $shadowed_nfa_edges{$nfa_edge} = 1;
        }

        my $to = $nfa_edge->[-1];
        my $bc = pc2bc($to);
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
        my ($nchars, $nholes) = count_chars_and_holes_in_ranges($dfa_edge->{char_ranges});
        $dfa_edge->{nchars} = $nchars;
        $dfa_edge->{nholes} = $nholes;
        #warn "nchars: ", $nchars, ", nholes: $nholes";
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

    my @actions;
    {
        my %seen;
        for my $nfa_edge (@$nfa_edges) {
            if (!defined $assert_info) {
                for my $pc (@$nfa_edge) {
                    my $bc = pc2bc($pc);
                    if (ref $bc && $bc->[0] =~ /cnt/) {
                        #warn "HIT $bc->[0]";
                        if (!$seen{abs $pc}) {
                            push @actions, $bc;
                            $seen{abs $pc} = 1;
                        }
                    }
                }
            }
        }
        if (@actions) {
            @actions = sort { $action_prio{$a->[0]} <=> $action_prio{$b->[0]} } @actions;
        }
    }

    if (!defined $assert_info) {
        $nfa_edges = dedup_nfa_edges($nfa_edges);
        $dfa_edge->{nfa_edges} = $nfa_edges;
    }

    {
        my (%seen_counting_states, @new_nfa_edges, $found);
        for my $nfa_edge (@$nfa_edges) {
            my $last = $nfa_edge->[-1];
            my $new_last;
            if ($counter_sets{$last}) {  # found a counting NFA state
                $new_last = $seen_counting_states{abs $last};
                if (!defined $new_last) {
                    my $first = $nfa_edge->[0];
                    my $bc = pc2bc($first);
                    if (ref $bc && $bc->[0] eq 'assert' && $bc->[-2] eq 'n ne') {
                        # inccnt first
                        if ($from_node->{idx} == 11) {
                            #warn "inccnt: $from_node->{idx} -> $$idx_ref: $last";
                        }
                        if ($last < 0) {
                            $new_last = -$last;
                        }

                    } else {
                        # addcnt first
                        if ($from_node->{idx} == 11) {
                            #warn "addcnt: $from_node->{idx} -> $$idx_ref: $last";
                        }
                        # so...we do nothing
                        if ($last > 0) {
                            $new_last = -$last;
                        }
                    }
                    $seen_counting_states{abs $last} = $new_last // $last;
                }
            }
            my $new_nfa_edge;
            if (defined $new_last && $new_last ne $last) {
                $found = 1;
                $new_nfa_edge = [@$nfa_edge];
                $new_nfa_edge->[-1] = $new_last;
            } else {
                $new_nfa_edge = $nfa_edge;
            }
            push @new_nfa_edges, $new_nfa_edge;

            if ($from_node->{idx} == 11) {
                #warn "found hit (11 -> $$idx_ref): ", Dumper($new_nfa_edge);
            }
        }

        if ($found) {
            $nfa_edges = \@new_nfa_edges;
            #warn "Found alternated NFA edge $from_node->{idx} -> $$idx_ref: ", Dumper($nfa_edges);
            $dfa_edge->{nfa_edges} = $nfa_edges;
        }

        #if ($from_node->{idx} == 1 && $$idx_ref == 4) {
            #warn "1 -> 4: ", Dumper($nfa_edges);
            #}
    }

    my @states;
    {
        my %seen;
        for my $nfa_edge (@$nfa_edges) {
            my $state = $nfa_edge->[-1];
            if (!exists $seen{$state}) {
                $seen{$state} = 1;
                push @states, $state;
            }
        }
    }

    if (@actions) {
        #warn "Found actions for edge ", gen_dfa_edge_label($from_node, $dfa_edge);
        $dfa_edge->{actions} = \@actions;
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
            if ($target_dfa_node->{idx} == 2 && $from_node->{idx} == 4) {
                #warn "DFA node 2 (from $from_node->{idx}): nfa nodes: ", Dumper($nfa_nodes);
                #warn Dumper($from_node);
                #warn "NFA edges from DFA node ", $from_node->{idx}, " to 2: ", Dumper($nfa_edges);
                #warn "dfa edge: ", Dumper($dfa_edge);
                #warn "===================";
            }
            $dfa_edge->{target} = $target_dfa_node;
            return $dfa_edge;
        }
    }

    my %target_countings;
    for my $state (@states) {
        my $count = $counter_sets{$state};
        if (defined $count) {
            #warn "Found counting state: $state ($count)\n";
            $target_countings{abs $state} = $count;
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
            #die $nfa_idx if $nfa_idx < 0;
            my $nfa_node = first { $_->{idx} eq $nfa_idx } @{ $nfa->{nodes} };
            push @$nfa_nodes, $nfa_node;
        }
    }
    $target_dfa_node = {
        defined $assert_info
            ? (assert_info => $assert_info,
               orig_source => $from_node->{idx},
               nfa_edges => $nfa_edges)
            : (nfa_nodes => $nfa_nodes,
               %target_countings ? (countings => \%target_countings) : ()),
        edges => undef,
        states => \@states,
        idx => $$idx_ref++,
        $is_accept ? (accept => 1) : (),
    };

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

    my @unshadowed;
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

    my %counting_asserts;
    my @bad_counter_assert_mask;
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
                if ($assert =~ /^cnt (\d+)/) {
                    my $id = $1;
                    my $prev_idx = $counting_asserts{$id};
                    if (defined $prev_idx) {
                        #warn "Found invalid comb";
                        push @bad_counter_assert_mask, (1 << $idx) | (1 << $prev_idx);
                    } else {
                        $counting_asserts{$id} = $idx;
                    }
                }
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

    my %bad_assert_settings;
    my $max_encoding = 2 ** $assert_idx - 1;
    for (my $comb_encoding = 0; $comb_encoding <= $max_encoding; $comb_encoding++) {
        for my $mask (@bad_counter_assert_mask) {
            if (($comb_encoding & $mask) == 0) {
                #warn "remove bad assert setting: $comb_encoding";
                $bad_assert_settings{$comb_encoding} = 1;
            }
        }
    }

    #warn $assert_idx;

    if ($assert_idx) {
        if ($assert_idx > 64) {
            die "Too many assertions: a $assert_idx-bit bitmap is required ",
                "but at most 64-bit is supported.\n";
        }

        #warn "asserts: ", Dumper(%asserts);
        return {
            assert_nfa_edges => \@assert_nfa_edges,
            uniq_assert_cnt => $assert_idx,
            asserts => \%asserts,
            bad_assert_settings => \%bad_assert_settings,
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
    #return $nfa_edges;
    my (%visited, @ret);
    for my $e (@$nfa_edges) {
        my $last = abs $e->[-1];
        my $counting = $counter_sets{$last};
        if (defined $counting) {
            my ($addcnt, $inccnt);
            for my $pc (@$e) {
                my $bc = pc2bc($pc);
                if (ref $bc) {
                    my $op = $bc->[0];
                    if ($op eq 'addcnt') {
                        $addcnt = $bc->[1];
                    } elsif ($op eq 'inccnt') {
                        $inccnt = $bc->[1];
                    }
                }
            }
            my $key;
            if (defined $addcnt) {
                $key = "addcnt-$addcnt";
            } elsif (defined $inccnt) { # contains inccnt only (without addcnt)
                $key = "inccnt-$inccnt";
            } else {
                die "an NFA edge to a counting NFA state cannot have neither addcnt nor inccnt.";
            }
            #warn "dedup key: $key";
            if ($visited{$key}) {
                next;
            }
            $visited{$key} = 1;
            push @ret, $e;
            next;
        }

        if ($visited{$last}) {
            next;
        }
        my $bc = pc2bc($last);
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

sub draw_partial_dfa ($$) {
    my ($dfa, $route) = @_;

    my (%visited_nodes, %visited_edges);
    {
        my $prev_node;
        my $i = 0;
        for my $node_idx (@$route) {
            #warn "Found visited node idx $node_idx";
            $visited_nodes{$node_idx} = 1;
            if (!defined $prev_node) {
                # first node
            } else {
                # got a new edge
                my $key = "$prev_node-$node_idx";
                my $values = $visited_edges{$key};
                my $v = ++$i;
                if (defined $values) {
                    push @$values, $v;
                } else {
                    $values = [$v];
                    $visited_edges{$key} = $values;
                }
            }
        } continue {
            $prev_node = $node_idx;
        }
    }

    my $dfa_nodes = $dfa->{nodes};

    undef $node_attr->{height};
    undef $edge_attr->{arrowsize};

    my $graph = GraphViz->new(
        layout => 'neato',
        ratio => 'auto',
        node => $node_attr,
        edge => $edge_attr,
    );

    my @nodes_to_draw;
    {
        my %seen;
        for my $node (@$dfa_nodes) {
            my $from_idx = $node->{idx};
            next unless defined $visited_nodes{$from_idx};
            next if $seen{$from_idx};
            $seen{$from_idx} = 1;
            push @nodes_to_draw, $node;
            $visited_nodes{$from_idx} = $node;
            for my $edge (@{ $node->{edges} }) {
                my $target = $edge->{target};
                my $to_idx = $target->{idx};
                if (!$seen{$to_idx} && !$visited_nodes{$to_idx}) {
                    $seen{$to_idx} = 1;
                    push @nodes_to_draw, $target;
                }
                my $shadowing = $edge->{shadowing};
                if (defined $shadowing) {
                    #my $label = gen_dfa_edge_label($node, $shadowing);
                    my $target = $shadowing->{target};
                    my $to_idx = $target->{idx};
                    if (!$seen{$to_idx} && !$visited_nodes{$to_idx}) {
                        $seen{$to_idx} = 1;
                        push @nodes_to_draw, $target;
                    }
                }
            }
        }
    }

    #@nodes_to_draw = uniq @nodes_to_draw;

    for my $node (@nodes_to_draw) {
        my $idx = $node->{idx};
        my $countings = $node->{countings};
        my $style;
        if ($countings) {
            $style = 'filled,dashed';
        }
        my $visited = $visited_nodes{$idx};
        my $label = gen_dfa_node_label($node);
        $graph->add_node("n$idx", $node->{start} ? (color => 'orange') : (),
                         $visited ? ($node->{assert_info} ? (fillcolor => 'orange')
                                                          : ())
                                  : (fillcolor => 'white'),
                         $node->{accept} ? (shape => 'doublecircle') : (),
                         label => $label || " " . $label,
                         defined $style ? (style => $style) : ());
    }

    for my $node (@nodes_to_draw) {
        my $from_idx = $node->{idx};
        next unless defined $visited_nodes{$from_idx};
        for my $e (@{ $node->{edges} }) {
            my $label = gen_dfa_edge_label($node, $e);
            my $to = $e->{target};
            my $to_idx = $to->{idx};
            my $visited = $visited_edges{"$from_idx-$to_idx"};
            if (defined $visited) {
                $label = join("", map { "($_)" } @$visited) . " $label";
            }
            $graph->add_edge("n$from_idx" => "n$to_idx", label => $label,
                             $visited ? () : (color => 'grey'),
                             len => max(length($label) / 7.5, 1.9));
            my $shadowing = $e->{shadowing};
            if (defined $shadowing) {
                #my $label = gen_dfa_edge_label($node, $shadowing);
                my $to = $shadowing->{target};
                my $to_idx = $to->{idx};
                my $visited = $visited_edges{"$from_idx-$to_idx"};
                if (defined $visited) {
                    $label = join("", map { "($_)" } @$visited) . " $label";
                }
                $graph->add_edge("n$from_idx" => "n$to_idx", label => $label,
                                 len => max(length($label) / 6, 1.7),
                                 $visited ? () : (color => 'black'),
                                 style => 'dashed');
            }
        }
    }

    my $outfile = "dfa-partial.png";
    $graph->as_png($outfile);

}

sub draw_dfa ($) {
    my ($dfa) = @_;

    my $dfa_nodes = $dfa->{nodes};

    my $big;
    if (@$dfa_nodes >= 25) {
        $node_attr->{height} = 0.1;
        $edge_attr->{arrowsize} = 0.5;
        $big = 1;
    } else {
        undef $node_attr->{height};
        undef $edge_attr->{arrowsize};
    }

    my $graph = GraphViz->new(
        layout => $big ? 'twopi' : 'neato',
        ratio => 'auto',
        node => $node_attr,
        edge => $edge_attr,
    );

    for my $node (@$dfa_nodes) {
        my $idx = $node->{idx};
        my $countings = $node->{countings};
        my $style;
        if ($countings) {
            $style = 'filled,dashed';
        }
        my $label = gen_dfa_node_label($node);
        $graph->add_node("n$idx", $node->{start} ? (color => 'orange') : (),
                         $node->{assert_info} ? (fillcolor => 'orange') : (),
                         $node->{accept} ? (shape => 'doublecircle') : (),
                         label => $big ? '' : $label || " " . $label,
                         defined $style ? (style => $style) : ());
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
    my $actions = $edge->{actions};
    my $label_suffix = '';
    if (defined $actions) {
        $label_suffix .= "| " . join ",", map { $action_labels{$_->[0]} // "unknown" } @$actions;
    }
    my $assert_settings = $edge->{assert_settings};
    if (defined $assert_settings) {
        # must be the assert results
        my $assert_info = $from_node->{assert_info} or die;
        my $asserts = $assert_info->{asserts} or die;
        my @labels;
        for my $assert (sort keys %$asserts) {
            my $idx = $asserts->{$assert};
            my $label = $assert;
            if ($label =~ /^cnt /) {
                # assertions for counting FAs.
                my @args = split / +/, $label;
                my $op;
                if ($args[-2] eq 'eq') {
                    $op = '=';
                } else {
                    $op = '≠';
                }
                my $val = $args[-1];
                $label = "cnt$op$val";
            }
            $label =~ s/\\/\\\\/g;
            if (!($assert_settings & (1 << $idx))) {
                $label = "!$label";
            }
            push @labels, $label;
        }
        #warn "labels: @labels";
        return join(",", @labels) . $label_suffix;
    }
    if ($edge->{to_accept}) {
        # epsilon edge to an "accept" state
        return "ɛ" . $label_suffix;
    }
    my $ranges = $edge->{char_ranges};
    #warn "range size: ", scalar @bits;
    return escape_range($ranges, 0) . $label_suffix;
}

sub gen_dfa_node_label ($) {
    my ($node) = @_;
    #if ($node->{start}) {
    #return "0";
    #}
    my @lines = "{" . join(",", uniq @{ $node->{states} }) . "}";
    push @lines, $node->{idx};
    if ($debug == 2 && defined $node->{min_len}) {
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
            if ($range->[0] == 0 && $range->[1] == 255) {
                return '*';
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
#include <stdint.h>
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
#
#define nelems(arr)     (sizeof(arr) / sizeof((arr)[0]))


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
        /* the "volatile" keyword is just to avoid the C compiler from
         * optimizing our useless loop away.
         */
        size_t          rest;
        volatile int    i;

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

    free(buf);

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

    # emit counter sets
    for my $id (sort keys %counter_sets) {
        next if $id < 0;
        my $count = $counter_sets{$id};
        my $ncounters = $count;
        # we need one more element because capturing code runs before counter handling
        # code and the former may add a new counter exceeding the limit.
        my $ncnt_ovecs = $count + 1;
        $src .= <<_EOC_;

    static short       counter_set_$id\[$ncounters];
    short             *oldest_counter_for_$id = counter_set_$id;
    short             *next_counter_for_$id = counter_set_$id;
    static int         counter_ovec_set_$id\[$ncnt_ovecs][$nvec];
    int              (*oldest_counter_ovec_for_$id)[$nvec] = counter_ovec_set_$id;
    int              (*next_counter_ovec_for_$id)[$nvec] = counter_ovec_set_$id;
_EOC_
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

    $src .= qq{    fprintf(stderr, "* entering state $label (i=%d len=%d)\\n", i, (int) len);\n} if $debug;

    my $used_error;

    if (@$edges == 2) {
        # try to apply memchr optimization
        my ($a, $b) = @$edges;
        my $a_ranges = $a->{char_ranges};
        if (!$a->{to_accept}
            && @$a_ranges == 2
            && $a_ranges->[0] == $a_ranges->[1]
            && !defined $a->{target}{assert_info}
            && !$b->{target}{assert_info}
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

    my $gen_read_char = 1;

    if (@$edges >= 2) {
        # try to apply the bit-map multi-char search optimization
        # TODO: we need better heuristics to choose between branch tables and
        # bitmaps.
        my $last = $edges->[-1];
        if (!defined $last->{assert_info}
            && $last->{default_branch}
            && $last->{target} eq $node)
        {
            my $max_nchars = 100;
            my $min_nchars = 3;
            my $max_holes_ratio = 0.3;
            my $ok = 1;
            my $total_holes = 0;
            my $total_chars = 0;
            for (my $i = 0; $i < @$edges - 1; $i++) {
                my $e = $edges->[$i];
                if ($e->{to_accept} || defined $e->{target}{assert_info}) {
                    undef $ok;
                    last;
                }
                my $nchars = $e->{nchars};
                if ($total_chars + $nchars > $max_nchars) {
                    undef $ok;
                    last;
                }
                $total_chars += $nchars;
                $total_holes += $e->{nholes};
            }

            if ($ok) {
                if ($total_chars < $min_nchars) {
                    undef $ok;
                } elsif ($total_chars >= 5 && $total_holes / $total_chars <= $max_holes_ratio) {
                    #warn "DFA node $node->{idx}: small holes ratio: ",
                        #$total_holes / $total_chars, ", falling back to jump table";
                    undef $ok;
                }
            }

            if ($ok) {
                #warn "HIT bit-map: $re: $idx: ", gen_dfa_node_label($node);

                # generate the start byte bitmap
                my @bitmap;  # with 256 bits, 32 bytes.
                for (my $i = 0; $i < @$edges - 1; $i++) {
                    my $e = $edges->[$i];
                    my $ranges = $e->{char_ranges};
                    for (my $i = 0; $i < @$ranges; $i += 2) {
                        my ($a, $b) = ($ranges->[$i], $ranges->[$i + 1]);
                        for (my $c = $a; $c <= $b; $c++) {
                            my $idx = $c >> 3;
                            my $byte = $bitmap[$idx];
                            if (!defined $byte) {
                                $byte = 0;
                            }
                            $byte |= (1 << ($c & 7));
                            $bitmap[$idx] = $byte;
                        }
                    }
                }

                $last->{memchr} = 1;
                my ($last_handler_src) =
                    gen_c_from_dfa_edge($node, $last, $level, $nvec, undef);
                delete $last->{memchr};

                $src .= <<_EOC_;
    {
        /* shortcut: search for multiple chars with a bitmap. */

        static const u_char bitmap_$idx\[32] = {
_EOC_

                my $indent = " " x (4 * 3);
                for (my $i = 0; $i < 32; $i += 4) {
                    my ($a, $b, $c, $d) = ($bitmap[$i], $bitmap[$i + 1], $bitmap[$i + 2], $bitmap[$i + 3]);
                    $a //= 0;
                    $b //= 0;
                    $c //= 0;
                    $d //= 0;
                    $src .= $indent . "$a, $b, $c, $d";
                    if ($i + 4 != 32) {
                        $src .= ",\n";
                    } else {
                        $src .= "\n" . (" " x (4 * 2)) . "};\n\n";
                    }
                }

                # TODO: use assembly to do faster dword/qword scanning.
                $src .= <<_EOC_;
        for (; i < len; i++) {
            c = s[i];
            if ((bitmap_$idx\[c >> 3] & (1 << (c & 7))) != 0) {
                break;
            }
        }

        if (unlikely(i == len)) {
            goto st${idx}_error;
        }
    }

$last_handler_src
    i++;
_EOC_
                $used_error = 1;
                $edges->[-2]{default_branch} = 1;
                pop @$edges;  # FIXME: do not taint DFA
                undef $gen_read_char;
            }
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

    if ($gen_read_char && @$edges) {
        if ($edges->[0]{to_accept}) {
            $src .= "    c = i < len ? s[i++] : (i++, -1);\n";
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
        }

        if ($debug) {
            $src .= qq{    fprintf(stderr, "reading new char %d (offset %d)\\n", c, i - 1);\n};
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

    if ($seen_accept) {
        if (@$edges > 1) {
            $src .= "    }\n";
            $level--;
        }
        if ($debug) {
            my $e = $edges->[0];
            die unless $e->{to_accept};
            my $target = $e->{target};
            my $label = gen_dfa_node_label($target);
            $label =~ s/\\n/ /g;
            $src .= <<_EOC_;
    fprintf(stderr, "* entering accept state $label (i=%d len=%d)\\n", i, (int) len);
_EOC_
        }
    }

closing_state:

    $src .= "    }  /* end state */\n\n";

    if ($used_error) {
        $src .= "st${idx}_error:\n";
    }

    my $indent = '';
    $src .= "    if (matched_0 != -1) {\n";
    $indent = '    ';

    for (my $i = 0; $i < $nvec; $i++) {
        my $assign = "    ovec[$i] = matched_$i;";
        $src .= $indent . "$assign\n";
        if ($debug > 1) {
            $src .= $indent . qq{    fprintf(stderr, "$assign\\n");\n};
        }
    }

    $src .= $indent . "    return MATCHED;  /* fallback */\n";

    $src .= <<'_EOC_';
    }
    return NO_MATCH;
_EOC_

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
            if ($debug) {
                $src .= qq{${indent}    fprintf(stderr, "hit \\"check to-accept\\" sibling (to $target->{idx})\\n");\n};
            }

            for (my $i = 0; $i < $nvec; $i++) {
                my $assign = "    ovec[$i] = matched_$i;";
                $src .= $indent . "$assign\n";
                if ($debug > 1) {
                    $src .= $indent . qq{    fprintf(stderr, "$assign\\n");\n};
                }
            }

            $src .= $indent . "    return MATCHED;\n";
            $src .= $indent . "}\n";

        } else {
            my $shadowing = $edge->{shadowing};
            if (defined $shadowing) {
                my $indent = $indents[$indent_idx];
                $src .= $indent . "if (asserts != 1) { /* shadowed DFA edge */\n";
                if ($debug) {
                    $src .= qq{${indent}    fprintf(stderr, "hit shadowed DFA edge to $target->{idx}\\n");\n};
                }
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
    my $left_is_ln_start = $from_node->{left_is_ln_start};

    #warn "left is ln start: ", $left_is_ln_start;

    my $assert_info = $target->{assert_info};
    my $indent = $indents[$indent_idx];

    if (defined $assert_info) {
        my $asserts = $assert_info->{asserts};
        $src .= $indent . "uint64_t asserts = 0;\n";
        my $min_len = $from_node->{min_len} // die;
        for my $assert (sort keys %$asserts) {
            my $idx = $asserts->{$assert};
            if ($assert eq '^') {
                #warn "found ^: $from_node->{start}: [$left_is_ln_start]";
                if ($from_node->{start}) {
                    #warn "HIT start";
                    $src .= $indent . "asserts |= 1 << $idx;\n";
                } elsif (defined $left_is_ln_start && $left_is_ln_start != -1) {
                    #warn "HIT left is ln start: $left_is_ln_start ",
                    #gen_dfa_node_label($from_node), " => ",
                    #gen_dfa_node_label($edge->{target});

                    if ($left_is_ln_start == 1) {
                        $src .= $indent . 'asserts |= (1 << ' . "$idx);\n";
                    } else {
                        # do nothing, since the result is always 0.
                    }

                } elsif ($min_len >= 1) {
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
            } elsif ($assert =~ /^cnt /) {
                my @args = split /\s+/, $assert;
                #die "args: @args";
                my $set_id = $args[1];
                my $n = $args[-1];
                my $op = $args[-2];
                # TODO: we could avoid duplicate evaluations if the both sides of the assertions
                # exist in a single DFA edge.
                if ($op eq 'eq') {
                    $src .= $indent . "asserts |= (*oldest_counter_for_$set_id == $n) << $idx;\n";
                } else {
                    $src .= $indent . "asserts |= (*oldest_counter_for_$set_id != $n "
                            . "|| next_counter_for_$set_id - oldest_counter_for_$set_id > 1) << $idx;\n";
                }
                #warn "Found assertion $assert";
            } else {
                die "TODO unknown assertion: $assert";
            }
            $src .= $indent . qq{fprintf(stderr, "assertion $assert test result: %lld, idx = $idx, i = %d, c = %d\\n", (long long) asserts, i, c);\n}
                if $debug;
        }

        my $assert_edges = $target->{edges};

        #warn "assert edges: $assert_edges\n";

        #warn "$edge: ", $target->{max_assert_settings}, " vs ", scalar @$assert_edges;
        my $use_default = (@$assert_edges == $target->{max_assert_settings} + 1);
        for my $subedge (@$assert_edges) {
            my $assert_settings = $subedge->{assert_settings};
            #die unless ref $assert_settings;
            my $sub_target = $subedge->{target};
            my $indent2;
            if ($use_default && $subedge eq $assert_edges->[-1]) {
                $src .= $indent . "{ /* asserts == $assert_settings */\n";
            } else {
                $src .= $indent . "if (asserts == $assert_settings) {\n";
            }
            $indent2 = $indent . (" " x 4);
            if ($debug) {
                $src .= qq{${indent2}fprintf(stderr, "hit assertion DFA node $target->{idx}\\n");\n};
            }
            if ($sub_target->{accept}) {
                $to_accept = 1;
            }
            $src .= gen_capture_handler_c_code($subedge, $sub_target->{accept}, $indent2, $nvec);
            if (!$to_accept) {
                # we don't care about cleanup for to-accept states.
                $src .= gen_edge_action_c_code($subedge, $indent2);
            }

            my $to = $sub_target->{idx};
            if (!$to_accept) {
                $src .= $indent2 . "goto st$to;\n";
            }
            $src .= $indent . "}\n";
        }

    } else {
        # normal DFA edge w/o assertions

        $src .= gen_capture_handler_c_code($edge, $to_accept, $indent, $nvec);
        if (!$to_accept) {
            $src .= gen_edge_action_c_code($edge, $indent);
        }

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
    my $nfa_edges = $edge->{nfa_edges};

    my %echo_values;
    my (%to_save_rows, %overwritten, @stores, %to_be_stored, %new_cnt_ovec);
    for my $mapping (@$mappings) {
        my ($from_row, $to_row, $from_pc, $to_pc) = @$mapping;

        my $nfa_edge = $nfa_edges->[$to_row];
        for my $pc (@$nfa_edge) {
            my $bc = pc2bc($pc);
            my $bcname = opcode($bc);
            if ($bcname eq 'save') {
                my $id = $bc->[1];
                if ($to_accept) {
                    push @stores, "matched_$id = i - 1;";
                    if ($debug > 1) {
                        $echo_values{"matched_$id"} = 1;
                    }
                } else {
                    my $to_var = gen_dst_cap_var($to_row, $id, $to_pc);
                    push @stores, "$to_var = i - 1;";
                    # TODO: skip newly initialized ovector in counter set states.
                    $to_be_stored{"$to_row-$id"} = 1;
                    if ($debug > 1) {
                        $echo_values{$to_var} = 1;
                    }
                }
            }
        }

        my $to_cntset;
        {
            my $counting = $counter_sets{$to_pc};
            if (defined $counting) {
                $to_cntset = abs $to_pc;
                $new_cnt_ovec{$to_cntset} = 1;
            }
        }

        my $from_cntset = $counter_sets{$from_pc};
        if (!$to_accept && ($from_row != $to_row || defined $to_cntset || defined $from_cntset)) {
            if ($overwritten{$from_row}) {
                $to_save_rows{$from_row} = 1;
            }
            if (!$to_be_stored{$to_row} && !defined $to_cntset) {
                $overwritten{$to_row} = 1;
            }
        }
    }

    %overwritten = ();

    my @transfers;
    for my $mapping (@$mappings) {
        my ($from_row, $to_row, $from_pc, $to_pc) = @$mapping;
        my $to_cntset = $counter_sets{$to_pc};
        my $from_cntset = $counter_sets{$from_pc};

        if ($to_accept) {
            my $t = $indent . "/* transfer caps from row $from_row ($from_pc) to matched */\n";
            for (my $i = 0; $i < $nvec; $i++) {
                my $from_var = gen_src_cap_var($from_row, $i, $from_pc);
                $t .= $indent . "matched_$i = $from_var;\n";
                if ($debug > 1) {
                    $echo_values{"matched_$i"} = 1;
                }
            }
            push @transfers, $t;

        } elsif ($from_row != $to_row || defined $to_cntset || defined $from_cntset) {
            my $t = $indent . "/* transfer caps from row $from_row ($from_pc) to row $to_row ($to_pc) */\n";
            for (my $i = 0; $i < $nvec; $i++) {
                if (!$to_be_stored{"$to_row-$i"}) {
                    my $to_var = gen_dst_cap_var($to_row, $i, $to_pc);
                    if ($to_save_rows{$to_row}) {
                        $t .= $indent . "tmp${to_row}_$i = $to_var;\n";
                    }
                    my $from_var;
                    if ($overwritten{$from_row} && !$to_be_stored{"$from_row-$i"}) {
                        # TODO: we could reuse the capsROW_COL variales here for temps
                        # if the source is a counter set ovector.
                        $from_var = "tmp${from_row}_$i";
                    } else {
                        $from_var = gen_src_cap_var($from_row, $i, $from_pc);
                    }
                    $t .= $indent . "$to_var = $from_var;\n";
                    if ($debug > 1) {
                        $echo_values{$to_var} = 1;
                    }
                }
            }
            if (!defined $to_cntset) {
                $overwritten{$to_row} = 1;
            }
            push @transfers, $t;
        }
    }

    if (%new_cnt_ovec) {
        for my $cntset (sort keys %new_cnt_ovec) {
            $src .= <<_EOC_;
${indent}/* add a new ovector to the counter set $cntset */
${indent}if (unlikely(next_counter_ovec_for_$cntset - counter_ovec_set_$cntset >= nelems(counter_ovec_set_$cntset))) {
${indent}    size_t     size;
${indent}    size = next_counter_ovec_for_$cntset - oldest_counter_ovec_for_$cntset;
${indent}    oldest_counter_ovec_for_$cntset = memmove(counter_ovec_set_$cntset,
${indent}                                        oldest_counter_ovec_for_$cntset,
${indent}                                        size * sizeof(counter_ovec_set_$cntset\[0]));
${indent}    next_counter_ovec_for_$cntset = counter_ovec_set_$cntset + size;
_EOC_

            if ($debug) {
                $src .= qq{${indent}fprintf(stderr, "re-organize counter ovec set $cntset.\\n");\n};
            }

            $src .= <<_EOC_;
${indent}}
${indent}next_counter_ovec_for_$cntset++;
_EOC_

            if ($debug) {
                $src .= qq{${indent}fprintf(stderr, "add new counter ovec for set $cntset.\\n");\n};
            }
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
        if ($debug > 1) {
            $src .= join "", map { (my $s = $_) =~ s/"/\\"/g;
                                   $s =~ s/\n/\\n/g;
                                   qq/${indent}fprintf(stderr, "$s\\n");\n/;
                                 } @transfers;
        }
        if (%to_save_rows) {
            $src .= $indent . "}\n";
        }
    }

    if (@stores) {
        $src .= $indent . "/* capture stores */\n";
        $src .= $indent . join("\n$indent", @stores) . "\n";
        if ($debug > 1) {
            $src .= $indent . qq{fprintf(stderr, "$indent/* capture stores */\\n");\n};
            $src .= $indent . join "\n$indent",
                                    map { (my $s = $_) =~ s/"/\\"/g;
                                          $s =~ s/\n/\\n/g;
                                          qq/fprintf(stderr, "$indent$s\\n");\n/;
                                        } @stores;
        }
    }

    if (%echo_values) {
        if (@stores) {
            $src .= $indent . qq/fprintf(stderr, "\\n");/;
        }
        for my $var (sort keys %echo_values) {
            $src .= $indent . qq/fprintf(stderr, "${indent}$var: %d\\n", $var);/;
        }
    }

    return $src;
}

sub gen_src_cap_var ($$$) {
    my ($row, $col, $pc) = @_;
    my $var;
    my $counting = $counter_sets{$pc};  # fetch counter set ID (if any)
    if (defined $counting) {
        $pc = abs $pc;
        $var = "oldest_counter_ovec_for_$pc\[0][$col]";
    } else {
        $var = "caps${row}_$col";
    }
    return $var;
}

sub gen_dst_cap_var ($$$) {
    my ($row, $col, $pc) = @_;
    my $var;
    my $counting = $counter_sets{$pc};  # fetch counter set ID (if any)
    if (defined $counting) {
        $pc = abs $pc;
        $var = "next_counter_ovec_for_$pc\[-1][$col]";
    } else {
        $var = "caps${row}_$col";
    }
    return $var;
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

    --repeat=N      repeat the operations for N times (default to 3) and also
                    pick the best timing result if the --timer option is
                    specified.

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

sub count_chars_and_holes_in_ranges ($) {
    my ($ranges) = @_;
    return (0, 0) unless defined $ranges;
    my $count = 0;
    my $holes = 0;
    my $prev_b;
    my $n = @$ranges;
    for (my $i = 0; $i < $n; $i += 2) {
        my ($a, $b) = ($ranges->[$i], $ranges->[$i + 1]);
        $count += $b - $a + 1;
        if (defined $prev_b) {
            $holes += $a - $prev_b - 1;
        }
        $prev_b = $b;
    }
    return ($count, $holes);
}

sub analyze_dfa ($) {
    my ($dfa) = @_;

    my $dfa_nodes = $dfa->{nodes};

    # check DFA edges from counting states to non-counting states (per counting NFA state)
    for my $node (@$dfa_nodes) {
        my $countings = $node->{countings};
        next unless defined $countings;
        my $dfa_edges = $node->{edges};
        my @edges = @$dfa_edges;
        for (my $i = 0; $i < @edges; $i++) {
            my $dfa_edge = $edges[$i];
            if ($dfa_edge->{shadowing}) {
                push @edges, $dfa_edge->{shadowing};
            }
            my @targets;
            my $target = $dfa_edge->{target};
            if (!defined $target->{nfa_nodes}) {
                my $sub_edges = $target->{edges};
                for my $sub_edge (@$sub_edges) {
                    push @targets, [$sub_edge->{target}, $sub_edge];
                }
            } else {
                push @targets, [$target, $dfa_edge];
            }
            for my $rec (@targets) {
                my ($target, $dfa_edge) = @$rec;
                my $target_countings = $target->{countings};
                #my $states = $target->{states};
                for my $nfa_state (sort keys %$countings) {
                    if (!defined $target_countings || !$target_countings->{$nfa_state}) {
                        #warn "Found clearing edge from $node->{idx} to $target->{idx} ",
                        #"for counter set $nfa_state\n";
                        #warn "add clrcnt action to DFA edge $node->{idx} => $target->{idx}: ";
                        my $actions = $dfa_edge->{actions};
                        if (!defined $actions) {
                            $actions = [["clrcnt", abs $nfa_state]];
                            $dfa_edge->{actions} = $actions;
                        } else {
                            #my $modified;
                            #for my $a (@$actions) {
                                #if ($a->[0] eq 'delcnt' && $a->[1] == $nfa_state) {
                                    #warn "remove redundant delcnt $nfa_state";
                                    #undef $a;
                                    #$modified = 1;
                                #}
                            #}
                            push @$actions, ["clrcnt", abs $nfa_state];
                            #if ($modified) {
                                #@$actions = grep { defined } @$actions;
                            #}
                        }
                    }
                }
            }
        }
    }

    # compute min/max length of input string consumed for each DFA node.
    # TODO: add proper support for the counting FA states.

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

sub dump_bytecode ($) {
    my ($bytecodes) = @_;
    my $n = length scalar @$bytecodes;
    my $pc = 0;
    my $s = '';
    for my $bc (@$bytecodes) {
        $s .= sprintf "%${n}d. ", $pc;
        if (ref $bc) {
            $s .= "@$bc\n";
        } elsif (defined $bc) {
            $s .= "$bc\n";
        } else {
            $s .= "nop\n";
        }
    } continue {
        $pc++;
    }
    return $s;
}

sub as_in_range_bytecode ($$) {
    my ($opcode, $args) = @_;
    if ($opcode eq 'in') {
        return ['in', @$args];
    }
    if ($opcode eq 'any') {
        return ["in", 0, 255];
    }
    if ($opcode eq 'char') {
        my $c = $args->[0];
        return ['in', $c, $c];
    }
    if ($opcode eq 'notin') {
        my $from = 0;
        my $found = 0;
        my @new_args;
        for (my $i = 0; $i < @$args; $i += 2) {
            my ($a, $b)  = ($args->[$i], $args->[$i + 1]);
            if ($from <= $a - 1) {
                push @new_args, $from, $a - 1;
            }
            $from = $b + 1;
            $found++;
        }
        if ($found && $from <= 255) {
            push @new_args, $from, 255;
        }
        return ['in', @new_args];
    }
    die "unknown opcode: $opcode\n";
}

sub rewrite_repetitions ($) {
    my $bytecodes = shift;
    my $found = 0;

    # find jump targets;
    my %jmp_targets;
    for my $bc (@$bytecodes) {
        if (ref $bc) {
            my $op = $bc->[0];
            if ($op eq 'jmp') {
                $jmp_targets{$bc->[1]}++;
            } elsif ($op eq 'split') {
                $jmp_targets{$bc->[1]}++;
                $jmp_targets{$bc->[2]}++;
            }
        }
    }

    my ($prev_args, $prev_args_str, $prev_opcode, $start_pc, $count);
    my $pc = 0;
    for my $bc (@$bytecodes) {
        if (defined $prev_opcode) {
            my $opcode = opcode($bc);
            #warn "opcode: $opcode, prev opcode: $prev_opcode";
            if ($opcode eq $prev_opcode && !$jmp_targets{$pc}) {
                if ($opcode eq 'any') {
                    #warn "Found successive any";
                    $count++;
                    next;
                }
                my @args = @$bc;
                shift @args;
                my $args_str = join ",", @args;
                if ($args_str eq $prev_args_str) {
                    $count++;
                    next;
                }
            }

            # found right boundary
            #warn "Found $count $pc";
            if ($count >= 2) {  # TODO: we need a more sensible threshold here
                $found++;
                #warn "HIT";
                my $bc = as_in_range_bytecode($prev_opcode, $prev_args);

                # directly fill the gap instead of appending to the bytecode
                # program if the gap is big enough.
                my $use_gap;
                if ($count >= 8) {
                    $use_gap = 1;
                }
                $count--;
                my $end = $use_gap ? $start_pc + 1 : @$bytecodes;
                my $counter_id = $end + 1;
                $counter_sets{$counter_id} = $count;
                $counter_sets{-$counter_id} = $count;  # for the counterpart
                $bytecodes->[$start_pc] = ["addcnt", $counter_id, $count];
                $start_pc++;
                if (!$use_gap) {
                    $bytecodes->[$start_pc] = ["jmp", $end];
                    $start_pc++;
                }
                my $saved_pc = $pc;
                my $pc = $end;
                $bytecodes->[$pc++] = ["inccnt", $counter_id];
                $bytecodes->[$pc++] = $bc;
                # the following NFA edge priority distinction is artifital and
                # will be resolved later during DFA construction. see
                # sub resolve_dfa_edge for details.
                $bytecodes->[$pc++] = ["split", $pc + 3, $pc + 1];
                $bytecodes->[$pc++] = ["assert", "cnt", $counter_id, "n ne", $count];
                $bytecodes->[$pc++] = ["jmp", $counter_id - 1];
                $bytecodes->[$pc++] = ["assert", "cnt", $counter_id, "n eq", $count];
                $bytecodes->[$pc++] = $bc;
                #$bytecodes->[$pc++] = ["delcnt", $counter_id];
                if (!$use_gap) {
                    $bytecodes->[$pc++] = ["jmp", $saved_pc];
                } else {
                    $start_pc = $pc;
                }
                for (my $i = $start_pc; $i < $saved_pc; $i++) {
                    $bytecodes->[$i] = "nop";
                }
            }

            undef $prev_opcode;
            undef $prev_args;
        }

        if (!defined $prev_opcode) {
            my $opcode = opcode($bc);
            if ($opcode =~ /^(?:char|any|(?:not)?in)$/) {
                $count = 1;
                $start_pc = $pc;
                $prev_opcode = $opcode;
                if ($opcode eq 'any') {
                    next;
                }
                my @args = @$bc;
                shift @args;
                $prev_args = \@args;
                $prev_args_str = join ",", @args;
            }
        }
    } continue {
        $pc++;
    }

    if ($found) {
        $used_asserts = 1;
    }

    return $found;
}

# FIXME: for now, we only have actions for counters.
# strictly speaking, capture handlings are also
# a kind of "actions". we might clear up the
# naming here in the future.
sub gen_edge_action_c_code ($$) {
    my ($edge, $indent) = @_;
    my $actions = $edge->{actions};
    my %inccnt;
    my $src = '';

    for my $action (@$actions) {
        my ($op, $set_id) = @$action;
        if ($op eq 'inccnt') {
            $inccnt{$set_id}++;
        }
    }

    for my $set_id (sort keys %inccnt) {
        my $count = $counter_sets{$set_id};
        # TODO: skip this operation if clrcnt is present.
        # TODO: remove the following branch test if possible
        $src .= <<_EOC_;
${indent}if (next_counter_for_$set_id != counter_set_$set_id && *oldest_counter_for_$set_id == $count) {
${indent}    oldest_counter_for_$set_id++;
${indent}    oldest_counter_ovec_for_$set_id++;
_EOC_

        if ($debug) {
            $src .= <<_EOC_;
${indent}    fprintf(stderr, "action: del oldest counter ovector from set $set_id.\\n");
${indent}    fprintf(stderr, "action: delcnt $set_id (olest counter: %d, %d counters).\\n",
${indent}            (int) *oldest_counter_for_$set_id,
${indent}            (int) (next_counter_for_$set_id - oldest_counter_for_$set_id));
_EOC_
        }

        $src .= <<_EOC_;
${indent}}
_EOC_
    }

    for my $action (@$actions) {
        my ($op, $set_id) = @$action;
        #warn "action: $op $set_id";
        if ($op eq 'addcnt') {
            $src .= <<_EOC_;
${indent}if (unlikely(next_counter_for_$set_id - counter_set_$set_id >= nelems(counter_set_$set_id))) {
${indent}    size_t     size;
${indent}    size = next_counter_for_$set_id - oldest_counter_for_$set_id;
${indent}    oldest_counter_for_$set_id = memmove(counter_set_$set_id,
${indent}                                         oldest_counter_for_$set_id,
${indent}                                         size * sizeof(counter_set_$set_id\[0]));
${indent}    next_counter_for_$set_id = counter_set_$set_id + size;
_EOC_

            if ($debug) {
                $src .= qq{${indent}fprintf(stderr, "re-organize counter set $set_id.\\n");\n};
            }

            $src .= <<_EOC_;
${indent}}
${indent}*next_counter_for_$set_id++ = 0;
_EOC_
        } elsif ($op eq 'inccnt') {
            $src .= <<_EOC_;
${indent}{
${indent}    short     *p;
${indent}    for (p = oldest_counter_for_$set_id; p < next_counter_for_$set_id; p++) {
${indent}        (*p)++;
${indent}    }
${indent}}
_EOC_
        } elsif ($op eq 'delcnt') {
            #$src .= "${indent}oldest_counter_for_$set_id++;\n";
        } else {
            die "unknown action: @$action" if $op ne 'clrcnt';
            $src .= <<_EOC_;
${indent}next_counter_for_$set_id = oldest_counter_for_$set_id = counter_set_$set_id;
${indent}next_counter_ovec_for_$set_id = oldest_counter_ovec_for_$set_id = counter_ovec_set_$set_id;
_EOC_
        }
        if ($debug) {
            $src .= <<_EOC_;
${indent}    fprintf(stderr, "action: @$action (olest counter: %d, %d counters).\\n",
${indent}            (int) *oldest_counter_for_$set_id,
${indent}            (int) (next_counter_for_$set_id - oldest_counter_for_$set_id));
_EOC_
        }
    }

    if ($debug) {
        for my $set_id (sort keys %inccnt) {
            $src .= <<_EOC_;
${indent}{
${indent}    short   *p;
${indent}    fprintf(stderr, "counter set $set_id:\\n");
${indent}    for (p = oldest_counter_for_$set_id; p < next_counter_for_$set_id; p++) {
${indent}        fprintf(stderr, "  counter #%d = %d\\n",
${indent}                (int) (p - oldest_counter_for_$set_id + 1), (int) *p);
${indent}    }
${indent}}
_EOC_
        }
    }

    return $src;
}

sub pc2bc ($) {
    my ($pc) = @_;
    if ($pc < 0) {
        return $bytecodes[-$pc];
    }
    return $bytecodes[$pc];
}
