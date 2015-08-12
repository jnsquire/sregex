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



=== TEST 5: testinput1:1523 (minimized)
--- re: .*.{3}
--- s eval: "abcde"



=== TEST 6: testinput1:1523 (minimized 2)
--- re: [^c]*.{3}
--- s eval: "Tccc"



=== TEST 7: testinput1:1523 (minimized 2)
--- re: [^c]*?.{3}
--- s eval: "Tccc"



=== TEST 8: re_tests:472 (3 + 1)
--- re: (a{3})+
--- s eval: "aaaa"



=== TEST 9: re_tests:472 (3 + 2)
--- re: (a{3})+
--- s eval: "aaaaa"



=== TEST 10: re_tests:472 (3 * 2 + 1)
--- re: (a{3})+
--- s eval: "aaaaaaa"



=== TEST 11: re_tests:916 (minimized)
--- re: .{3}a
--- s eval: "123\na"



=== TEST 12: re_tests:916 (minimized 2)
--- re: ^.{3}a
--- s eval: "\nabca"
