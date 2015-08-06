# vim:set ft= ts=4 sw=4 et fdm=marker:

use t::SRegex 'no_plan';

run_tests();

__DATA__

=== TEST 1: \&
--- re: a\&b
--- s eval: 'a&b'



=== TEST 2: [\&]
--- re: a[\&]b
--- s eval: 'a&b'



=== TEST 3: parallel 0-width assertions (1)
--- re eval: ' (?:(\b)|($))'
--- s eval: " a"
--- cap: (0, 1) (1, 1)



=== TEST 4: parallel 0-width assertions (2)
--- re eval: ' (?:(\b)|($))'
--- s eval: " \n"
--- cap: (0, 1) (-1, -1) (1, 1)
