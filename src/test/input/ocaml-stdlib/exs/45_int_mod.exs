// 0_basics.types, 1_comparison.types, 6_float.types, 7_str.types, 45_int_mod.exs

// Constants
zero
one
minus_one
max_int
min_int

// Unary arithmetic: int -> int
(neg Num)
(succ Num)
(pred Num)
(abs Num)
(neg zero)
(succ one)
(pred minus_one)
(abs minus_one)

// Binary arithmetic: int -> int -> int
(add Num Num)
(sub Num Num)
(mul Num Num)
(div Num Num)
(rem Num Num)
(add zero Num)
(sub Num one)
(mul minus_one Num)

// Bitwise: int -> int -> int / int -> int
(logand Num Num)
(logor Num Num)
(logxor Num Num)
(lognot Num)
(shift_left Num Num)
(shift_right Num Num)
(shift_right_logical Num Num)

// Comparison: int -> int -> bool / int
(equal Num Num)
(compare Num Num)
(min Num Num)
(max Num Num)
(equal zero Num)
(compare one Num)
(min max_int Num)
(max min_int Num)

// Conversions
(to_float Num)
(of_float Flt)
(to_string Num)
(to_float zero)
(to_float one)
(to_string zero)
(to_string max_int)

// Hash
(hash Num)
(seeded_hash Num Num)

// Chaining: unary ops return int
(neg (neg Num))
(abs (neg Num))
(succ (pred Num))
(pred (succ Num))
(neg (abs (sub Num Num)))

// Binary ops return int: chain them
(add (succ Num) (pred Num))
(mul (abs Num) (succ Num))
(sub (add Num Num) Num)
(rem (abs Num) (succ Num))
(logand (shift_left Num Num) (shift_right Num Num))
(lognot (logxor Num Num))
(add (logand Num Num) (logor Num Num))

// compare returns int: use in arithmetic
(= (compare Num Num) Num)
(succ (compare Num Num))
(< (compare Num Num) Num)
(add (compare Num Num) Num)
(compare (compare Num Num) Num)

// min/max return int: chain
(min (max Num Num) Num)
(max (min Num Num) Num)
(min (compare Num Num) Num)
(equal (min Num Num) Num)
(= (min Num Num) Num)
(succ (max Num Num))

// equal returns bool
(= (equal Num Num) true)
(not (equal Num Num))
(equal (compare Num Num) Num)

// to_float returns float: use in float arithmetic
(+. (to_float Num) Flt)
(+. (to_float Num) (to_float Num))
(= (to_float Num) Flt)

// of_float returns int: use in int arithmetic
(succ (of_float Flt))
(add (of_float Flt) Num)
(equal (of_float Flt) Num)

// to_string returns string: use in string ops
(= (to_string Num) Str)
(^ (to_string Num) Str)
(^ (to_string Num) (to_string Num))

// hash returns int
(= (hash Num) Num)
(succ (hash Num))
(seeded_hash (hash Num) Num)
(add (hash Num) (seeded_hash Num Num))

// Invalid: outputs used at wrong types
(+. (compare Num Num) Flt)
(succ (to_float Num))
(succ (equal Num Num))
(not (compare Num Num))
(not (min Num Num))
(^ (min Num Num) Str)
(to_float (equal Num Num))
(of_float (equal Num Num))
