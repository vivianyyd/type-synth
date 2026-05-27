// 0_basics.types, 7_str.types

((^) Str Str)
((^) ((^) Str Str) Str)
((^) Str ((^) Str Str))
((^) ((^) Str Str) ((^) Str Str))

((^) Num Str)
((^) Str Num)
((^) true Str)

// ^ returns string: chain further concatenations
((^) ((^) ((^) Str Str) Str) Str)
((^) Str ((^) Str ((^) Str Str)))
((^) ((^) Str Str) ((^) Str Str))
((^) ((^) ((^) Str Str) ((^) Str Str)) Str)

// invalid chaining
((^) ((^) Num Str) Str)
