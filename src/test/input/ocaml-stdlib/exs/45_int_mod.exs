// 0_basics.types, 1_comparison.types, 6_float.types, 7_str.types, 45_int_mod.exs

// Constants
Int.zero
Int.one
Int.minus_one
Int.max_int
Int.min_int

// Unary arithmetic: int -> int
(Int.neg Num)
(Int.succ Num)
(Int.pred Num)
(Int.abs Num)
(Int.neg Int.zero)
(Int.succ Int.one)
(Int.pred Int.minus_one)
(Int.abs Int.minus_one)

// Binary arithmetic: int -> int -> int
(Int.add Num Num)
(Int.sub Num Num)
(Int.mul Num Num)
(Int.div Num Num)
(Int.rem Num Num)
(Int.add Int.zero Num)
(Int.sub Num Int.one)
(Int.mul Int.minus_one Num)

// Bitwise: int -> int -> int / int -> int
(Int.logand Num Num)
(Int.logor Num Num)
(Int.logxor Num Num)
(Int.lognot Num)
(Int.shift_left Num Num)
(Int.shift_right Num Num)
(Int.shift_right_logical Num Num)

// Comparison: int -> int -> bool / int
(Int.equal Num Num)
(Int.compare Num Num)
(Int.min Num Num)
(Int.max Num Num)
(Int.equal Int.zero Num)
(Int.compare Int.one Num)
(Int.min Int.max_int Num)
(Int.max Int.min_int Num)

// Conversions
(Int.to_float Num)
(Int.of_float Flt)
(Int.to_string Num)
(Int.to_float Int.zero)
(Int.to_float Int.one)
(Int.to_string Int.zero)
(Int.to_string Int.max_int)

// Hash
(Int.hash Num)
(Int.seeded_hash Num Num)

// Chaining: unary ops return int
(Int.neg (Int.neg Num))
(Int.abs (Int.neg Num))
(Int.succ (Int.pred Num))
(Int.pred (Int.succ Num))
(Int.neg (Int.abs (Int.sub Num Num)))

// Binary ops return int: chain them
(Int.add (Int.succ Num) (Int.pred Num))
(Int.mul (Int.abs Num) (Int.succ Num))
(Int.sub (Int.add Num Num) Num)
(Int.rem (Int.abs Num) (Int.succ Num))
(Int.logand (Int.shift_left Num Num) (Int.shift_right Num Num))
(Int.lognot (Int.logxor Num Num))
(Int.add (Int.logand Num Num) (Int.logor Num Num))

// compare returns int: use in arithmetic
((=) (Int.compare Num Num) Num)
(Int.succ (Int.compare Num Num))
((<) (Int.compare Num Num) Num)
(Int.add (Int.compare Num Num) Num)
(Int.compare (Int.compare Num Num) Num)

// min/max return int: chain
(Int.min (Int.max Num Num) Num)
(Int.max (Int.min Num Num) Num)
(Int.min (Int.compare Num Num) Num)
(Int.equal (Int.min Num Num) Num)
((=) (Int.min Num Num) Num)
(Int.succ (Int.max Num Num))

// equal returns bool
((=) (Int.equal Num Num) true)
(not (Int.equal Num Num))
(Int.equal (Int.compare Num Num) Num)

// to_float returns float: use in float arithmetic
((+.) (Int.to_float Num) Flt)
((+.) (Int.to_float Num) (Int.to_float Num))
((=) (Int.to_float Num) Flt)

// of_float returns int: use in int arithmetic
(Int.succ (Int.of_float Flt))
(Int.add (Int.of_float Flt) Num)
(Int.equal (Int.of_float Flt) Num)

// to_string returns string: use in string ops
((=) (Int.to_string Num) Str)
((^) (Int.to_string Num) Str)
((^) (Int.to_string Num) (Int.to_string Num))

// hash returns int
((=) (Int.hash Num) Num)
(Int.succ (Int.hash Num))
(Int.seeded_hash (Int.hash Num) Num)
(Int.add (Int.hash Num) (Int.seeded_hash Num Num))

// Invalid: outputs used at wrong types
((+.) (Int.compare Num Num) Flt)
(Int.succ (Int.to_float Num))
(Int.succ (Int.equal Num Num))
(not (Int.compare Num Num))
(not (Int.min Num Num))
((^) (Int.min Num Num) Str)
(Int.to_float (Int.equal Num Num))
(Int.of_float (Int.equal Num Num))
