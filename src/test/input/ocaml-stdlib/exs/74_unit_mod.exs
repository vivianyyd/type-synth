// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 74_unit_mod.types

// equal: t -> t -> bool
(equal Unit Unit)

// compare: t -> t -> int
(compare Unit Unit)

// to_string: t -> string
(to_string Unit)

// Chaining: equal returns bool
(= (equal Unit Unit) true)
(not (equal Unit Unit))
(&& (equal Unit Unit) (equal Unit Unit))

// compare returns int
(= (compare Unit Unit) Num)
(succ (compare Unit Unit))
(< (compare Unit Unit) Num)

// to_string returns string
(= (to_string Unit) Str)
(^ (to_string Unit) Str)
(^ (to_string Unit) (to_string Unit))

// Invalid
(equal Num Unit)
(equal Unit Num)
(equal Str Str)
(compare Num Unit)
(to_string Num)
(succ (equal Unit Unit))
(not (compare Unit Unit))
