#!/usr/bin/env perl

use strict;
use warnings;

use IPC::Run3;
use Data::Dumper;
use GraphViz;
use List::MoreUtils qw( uniq firstidx );
use List::Util qw( first max );
use Carp qw( croak carp );

sub add_edges ($$$$);
sub gen_nfa_edge_label ($);
sub escape_char ($);
sub escape_range_char ($);
sub gen_nfa ();
sub draw_nfa ($);
sub is_node ($);
sub opcode ($);
sub gen_dfa_edges ($$$$$);
sub gen_dfa ($);
sub draw_dfa ($);
sub escape_range ($$);
sub gen_dfa_hash_key ($);
sub add_to_set ($$);
sub remove_from_set ($$);
sub gen_dfa_node_label ($);
sub gen_dfa_edge_label ($);

$Data::Dumper::Terse = 1;

my $re = shift
    or die "No regex specified.\n";

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

my $nfa = gen_nfa();
#warn Dumper($nfa);
draw_nfa($nfa);

my $dfa = gen_dfa($nfa);
warn Dumper($dfa);
draw_dfa($dfa);

sub gen_nfa () {
    my @nodes;
    my $idx = 0;
    for my $bc (@bytecodes) {
        my $opcode = is_node($bc);
        if (defined $opcode || $idx == 0) {
            my $node = {
                idx => $idx,
                edges => [],
                $idx == 0 ? (start => 1) : (),
            };
            if (defined $opcode && $opcode eq 'match') {
                $node->{accept} = 1;
            }
            push @nodes, $node;
        }
        $idx++;
    }

    for my $node (@nodes) {
        my %visited;
        my $idx = $node->{idx};
        add_edges($node, $idx == 0 ? 0 : $idx + 1, \%visited, undef);
    }

    return \@nodes;
}

sub draw_nfa ($) {
    my ($nfa) = @_;

    my $graph = GraphViz->new(
        layout => $big ? 'twopi' : 'neato',
        ratio => 'auto',
        node => $node_attr,
        edge => $edge_attr,
    );

    #$graph->as_dot("nfa.dot");
    for my $node (@$nfa) {
        my $idx = $node->{idx};
        $graph->add_node("n$idx", $node->{start} ? (color => 'orange') : (),
                         $node->{accept} ? (shape => 'doublecircle') : (),
                         label => $big ? '' : $idx || " $idx");
    }
    for my $node (@$nfa) {
        my $from_idx = $node->{idx};
        my $e_idx = 0;
        for my $e (@{ $node->{edges} }) {
            my $label = gen_nfa_edge_label($e);
            my $to_idx = $e->[-1];
            my $color = $edge_colors[$e_idx] || 'black';
            $graph->add_edge("n$from_idx" => "n$to_idx", label => $label, color => $color);
            $e_idx++;
        }
    }
    $graph->as_png("nfa.png");
}

sub add_edges ($$$$) {
    my ($from_node, $idx, $visited, $to_nodes) = @_;

    #warn "add edges: $from_node->{idx} => $idx";
    my $bc = $bytecodes[$idx];
    return unless defined $bc;

    my $opcode = opcode($bc);
    if (exists $visited->{$idx}) {
        if ($opcode eq 'split') {
            my $y = $bc->[2];
            if (!$visited->{$y}) {
                add_edges($from_node, $y, $visited, $to_nodes);
                return;
            }
        }
        return;
    }

    $visited->{$idx} = 1;

    if ($opcode eq 'jmp') {
        add_edges($from_node, $bc->[1], $visited, $to_nodes);
        return;
    }

    if ($opcode eq 'split') {
        my $x = $bc->[1];
        my $y = $bc->[2];
        my $forked = $to_nodes ? [@$to_nodes] : undef;
        add_edges($from_node, $x, $visited, $to_nodes);
        add_edges($from_node, $y, $visited, $forked);
        return;
    }

    if ($opcode eq 'save' or $opcode eq 'assert') {
        #warn Dumper \$bc;
        if (!defined $to_nodes) {
            $to_nodes = [];
        }
        push @$to_nodes, $idx;
        add_edges($from_node, $idx + 1, $visited, $to_nodes);
        return;
    }

    if (!defined $to_nodes) {
        $to_nodes = [];
    }
    push @$to_nodes, $idx;

    my $edge = $to_nodes;
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
                $label = '.';
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
    my $dfa_node = {
        nfa_nodes => [$nfa->[0]],
        edges => undef,
        idx => 0,
        start => 1,
    };
    my @dfa_nodes = ($dfa_node);
    my %dfa_node_hash;
    my $idx = 1;
    my $i = 0;
    while ($i < @dfa_nodes) {
        my $dfa_node = $dfa_nodes[$i];
        my $nfa_nodes = $dfa_node->{nfa_nodes};

        my @all_nfa_edges;
        for my $nfa_node (@$nfa_nodes) {
            my $idx = $nfa_node->{idx};
            my $edges = $nfa_node->{edges};
            if ($edges) {
                push @all_nfa_edges, @$edges;
            }
        }
        # de-duplicate elements in @all_nfa_edges?
        my $dfa_edges = gen_dfa_edges(\@dfa_nodes, \%dfa_node_hash, \@all_nfa_edges, $nfa, \$idx);
        $dfa_node->{edges} = $dfa_edges;
        $i++;
    }

    for my $dfa_node (@dfa_nodes) {
        delete $dfa_node->{nfa_nodes};
    }

    return \@dfa_nodes;
}

sub gen_dfa_edges ($$$$$) {
    my ($dfa_nodes, $dfa_node_hash, $nfa_edges, $nfa, $idx_ref) = @_;
    my %left_end_hash;
    my %right_end_hash;
    my %prio;
    my @endpoints;
    my $prio = 0;
    for my $nfa_edge (@$nfa_edges) {
        $prio{$nfa_edge} = $prio++;
        my $to = $nfa_edge->[-1];
        my $bc = $bytecodes[$to];
        my $opcode = opcode($bc);
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
            #warn "args: ", Dumper(\@args);
            my $from = 0;
            for (my $i = 0; $i < @args; $i += 2) {
                my ($a, $b)  = ($args[$i], $args[$i + 1]);
                push @endpoints, $a;
                add_to_hash(\%left_end_hash, $from, $nfa_edge);
                add_to_hash(\%right_end_hash, $a, $nfa_edge);
                $from = $b;
            }
            push @endpoints, $from;
            push @endpoints, 255;
            add_to_hash(\%left_end_hash, $from, $nfa_edge);
            add_to_hash(\%right_end_hash, 255, $nfa_edge);
        } elsif ($opcode eq 'match') {
            # TODO
        } else {
            die "unknown bytecode opcode: $opcode";
        }
    }
    @endpoints = uniq sort { $a <=> $b } @endpoints;
    #warn "left endpoint hash: ", Dumper(\%left_end_hash);
    #warn "right endpoint hash: ", Dumper(\%right_end_hash);
    #warn "endpoints: ", Dumper(\@endpoints);
    my (@active_nfa_edges, @dfa_edges, $prev);
    for my $p (@endpoints) {
        my $singular;
        my $right_nfa_edges = $right_end_hash{$p};
        if ($right_nfa_edges) {
            my @saved = @active_nfa_edges;
            if (remove_from_set(\@active_nfa_edges, $right_nfa_edges)) {
                warn "HERE right $p (prev $prev)";
                push @dfa_edges, [$prev, $p,
                    [sort { $prio{$a} <=> $prio{$b} } @saved]];
                if (@active_nfa_edges) {
                    $prev = $p + 1;
                }
            } else {
                warn "HERE singular right $p (prev $prev)";
                $singular = 1;
            }
        }
        my $left_nfa_edges = $left_end_hash{$p};
        if ($left_nfa_edges) {
            if (defined $prev) {
                warn "HERE left $p (prev $prev)";
                push @dfa_edges, [$prev, $p - 1,
                    [sort { $prio{$a} <=> $prio{$b} } @active_nfa_edges]];
            }
            add_to_set(\@active_nfa_edges, $left_nfa_edges);
            $prev = $p;
            if ($singular) {
                push @dfa_edges, [$prev, $p,
                    [sort { $prio{$a} <=> $prio{$b} } @active_nfa_edges]];
                remove_from_set(\@active_nfa_edges, $right_nfa_edges);
                $prev++;
            }
        }
    }

    my %targets;
    for my $dfa_edge (@dfa_edges) {
        my $target = $dfa_edge->[-1];
        #warn "DFA edge target: ", Dumper($target);
        my $key = gen_dfa_hash_key($target);
        warn "dfa state key: ", $key;
        my $old_edge = $targets{$key};
        if (defined $old_edge) {
            pop @$dfa_edge;
            splice @$old_edge, -1, 0, @$dfa_edge;
            $dfa_edge = undef;
            next;
        }
        $targets{$key} = $dfa_edge;
        my $target_dfa_node = $dfa_node_hash->{$key};
        if (!defined $target_dfa_node) {
            my @nfa_nodes;
            for my $nfa_edge (@$target) {
                my $nfa_idx = $nfa_edge->[-1];
                my $nfa_node = first { $_->{idx} eq $nfa_idx } @$nfa;
                push @nfa_nodes, $nfa_node;
            }
            $target_dfa_node = {
                nfa_nodes => \@nfa_nodes,
                edges => undef,
                actions => $target,
                idx => $$idx_ref++,
            };
            push @$dfa_nodes, $target_dfa_node;
            $dfa_node_hash->{$key} = $target_dfa_node;
        }
        $dfa_edge->[-1] = $target_dfa_node
    }

    @dfa_edges = grep { defined } @dfa_edges;
    #warn "DFA edges: ", Dumper(\@dfa_edges);
    return \@dfa_edges;
}

sub gen_dfa_hash_key ($) {
    my ($nfa_edges) = @_;
    #warn "nfa edges: ", Dumper($nfa_edges);
    my @bits;
    for my $nfa_edge (@$nfa_edges) {
        push @bits, join ",", @$nfa_edge;
    }
    return join "|", @bits;
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

    for my $node (@$dfa) {
        my $idx = $node->{idx};
        my $label = gen_dfa_node_label($node);
        $graph->add_node("n$idx", $node->{start} ? (color => 'orange') : (),
                         $node->{accept} ? (shape => 'doublecircle') : (),
                         label => $big ? '' : $label || "start");
    }

    for my $node (@$dfa) {
        my $from_idx = $node->{idx};
        for my $e (@{ $node->{edges} }) {
            my $label = gen_dfa_edge_label($e);
            my $to = $e->[-1];
            my $to_idx = $to->{idx};
            $graph->add_edge("n$from_idx" => "n$to_idx", label => $label,
                             len => max(length($label) / 6, 1));
        }
    }

    $graph->as_png("dfa.png");
}

sub gen_dfa_edge_label ($) {
    my ($edge) = @_;
    my @bits = @$edge;
    pop @bits;
    #warn "range size: ", scalar @bits;
    return escape_range(\@bits, 0);
}

sub gen_dfa_node_label ($) {
    my ($node) = @_;
    my @lines;
    for my $nfa_edge (@{ $node->{actions} }) {
        push @lines, join ",", @$nfa_edge;
    }
    return join "\\n", @lines;
}

sub escape_range ($$) {
    my ($range, $negate) = @_;
    my $s;
    if ($negate) {
        $s = "[^";
    } else {
        if (@$range == 2 && $range->[0] == $range->[1]) {
            return escape_char($range->[0]);
        }
        $s = "[";
    }
    for (my $i = 0; $i < @$range; $i += 2) {
        my $a = $range->[$i];
        my $b = $range->[$i + 1];
        if ($a == $b) {
            $s .= escape_range_char($a);
        } else {
            $s .= escape_range_char($a) . "-" . escape_range_char($b);
        }
    }
    $s .= "]";
}
