// 0-basics.types, 1-comparison.types, 7-str.types

(^ Str Str)
(^ (^ Str Str) Str)
(^ Str (^ Str Str))
(^ (^ Str Str) (^ Str Str))

(^ Num Str)
(^ Str Num)
(^ true Str)

// ^ returns string: chain further concatenations
(^ (^ (^ Str Str) Str) Str)
(^ Str (^ Str (^ Str Str)))
(^ (^ Str Str) (^ Str Str))
(^ (^ (^ Str Str) (^ Str Str)) Str)

// ^ output used as input to =
(= (^ Str Str) Str)
(= (^ Str Str) (^ Str Str))

// invalid chaining
(^ (^ Num Str) Str)
(= (^ Str Str) Num)
