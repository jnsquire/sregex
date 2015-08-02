# vim:set ft= ts=4 sw=4 et fdm=marker:

use t::SRegex 'no_plan';

run_tests();

__DATA__

=== TEST 1: parallel 0-width assertions (1)
--- re eval: ' (?:(\b)|($))'
--- s eval: " a"
--- cap: (0, 1) (1, 1)



=== TEST 2: parallel 0-width assertions (2)
--- re eval: ' (?:(\b)|($))'
--- s eval: " \n"
--- cap: (0, 1) (-1, -1) (1, 1)
