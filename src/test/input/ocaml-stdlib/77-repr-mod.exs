// 0-basics.types, 1-comparison.types, 4-arith.types, 7-str.types, 77-repr-mod.types

// phys_equal: 'a -> 'a -> bool
(phys_equal Num Num)
(phys_equal Str Str)
(phys_equal true true)

// equal: 'a -> 'a -> bool
(equal Num Num)
(equal Str Str)
(equal true true)
(equal Char Char)

// compare: 'a -> 'a -> int
(compare Num Num)
(compare Str Str)
(compare true false)

// min: 'a -> 'a -> 'a
(min Num Num)
(min Str Str)
(min true false)

// max: 'a -> 'a -> 'a
(max Num Num)
(max Str Str)
(max true false)

// Chaining: equal/phys_equal return bool
(= (equal Num Num) true)
(not (equal Num Num))
(&& (equal Num Num) (phys_equal Num Num))
(|| (equal Str Str) (equal Num Num))
(not (phys_equal Str Str))

// compare returns int
(= (compare Num Num) Num)
(succ (compare Num Num))
(< (compare Num Num) Num)
(+ (compare Num Num) (compare Str Str))

// min/max return same type as inputs
(= (min Num Num) Num)
(succ (min Num Num))
(^ (min Str Str) Str)
(not (min true false))
(min (min Num Num) Num)
(max (min Num Num) (max Num Num))
(= (min Num Num) (max Num Num))
(compare (min Num Num) (max Num Num))
(equal (min Num Num) (max Num Num))

// Invalid
(phys_equal Num Str)
(equal Num Str)
(compare Num Str)
(min Num Str)
(max Num Str)
(succ (equal Num Num))
(not (compare Num Num))
