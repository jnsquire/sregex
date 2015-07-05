#!/usr/bin/env perl

use strict;
use warnings;

use IPC::Run3;
#use Data::Dumper;
use GraphViz;
use Carp qw( croak carp );

sub add_edges ($$$$);
sub gen_label ($);
sub escape_char ($);
sub gen_nfa ();
sub draw_nfa ($);
sub is_node ($);
sub opcode ($);

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
            push @bytecodes, [$opcode, split /\s*,\s+/, $args];

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
my %escapes = (
    "\t" => '\t',
    "\n" => '\n',
    " " => '\ ',
    "\e" => '\e',
    "\f" => '\f',
    "\\" => "\\",
    "^" => "'^'",
    '$' => "'\$'",
    '(' => "'('",
    ')' => "')'",
    '[' => "'['",
    ']' => "']'",
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
    $edge_attr->{minlen} = 2.5;
}

my $nfa = gen_nfa();
#warn Dumper($nfa);
draw_nfa($nfa);

sub gen_nfa () {
    my @nodes;
    my $idx = 0;
    for my $bc (@bytecodes) {
        my $opcode = is_node($bc);
        if (defined $opcode || $idx == 0) {
            my $node = {
                idx => $idx,
                edges => [],
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
        $graph->add_node("n$idx", $idx == 0 ? (color => 'orange') : (),
                         $node->{accept} ? (shape => 'doublecircle') : (),
                         label => $big ? '' : $idx || " $idx");
    }
    for my $node (@$nfa) {
        my $from_idx = $node->{idx};
        my $e_idx =0;
        for my $e (@{ $node->{edges} }) {
            my $label = gen_label($e);
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

sub gen_label ($) {
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
                $label = escape_char($v);
            } elsif ($opcode eq 'in') {
                $label = range_to_str($v);
            } elsif ($opcode eq 'notin') {
                $label = range_to_str($v, 1);
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
    my $escaped = $escapes{$c};
    if (defined $escaped) {
        return "'$escaped'";
    }
    if ($c =~ /[[:alnum:]]/) {
        return "'$c'";
    }
    if ($c =~ /[[:print:]]/) {
        return "'$c'";
    }
    return sprintf("\\%03o", ord($c));
}
