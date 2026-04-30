// 0_basics.types, 1_comparison.types, 6_float.types, 7_str.types, 46_int32_mod.types

// Constants (type int32)
zero
one
minus_one
max_int
min_int

// Constructing int32 values
(of_int Num)
(of_float Flt)
(of_string Str)

// Unary: int32 -> int32
(neg zero)
(neg one)
(neg (of_int Num))
(abs (of_int Num))
(abs minus_one)
(succ zero)
(succ (of_int Num))
(pred one)
(pred (of_int Num))
(lognot (of_int Num))

// Binary: int32 -> int32 -> int32
(add zero one)
(add (of_int Num) (of_int Num))
(sub one zero)
(sub (of_int Num) (of_int Num))
(mul zero one)
(mul (of_int Num) (of_int Num))
(div one one)
(div (of_int Num) one)
(rem (of_int Num) one)
(unsigned_div (of_int Num) one)
(unsigned_rem (of_int Num) one)
(logand (of_int Num) (of_int Num))
(logor (of_int Num) (of_int Num))
(logxor (of_int Num) (of_int Num))

// Shifts: int32 -> int -> int32
(shift_left (of_int Num) Num)
(shift_right (of_int Num) Num)
(shift_right_logical (of_int Num) Num)

// Conversions to other types
(to_int zero)
(to_int one)
(to_int (of_int Num))
(to_float zero)
(to_float (of_int Num))
(to_string zero)
(to_string (of_int Num))

// Comparison: int32 -> int32 -> int / bool
(compare zero one)
(compare (of_int Num) (of_int Num))
(unsigned_compare (of_int Num) (of_int Num))
(equal zero one)
(equal (of_int Num) (of_int Num))
(min zero one)
(max zero one)
(min (of_int Num) (of_int Num))
(max (of_int Num) (of_int Num))

// hash
(hash (of_int Num))
(seeded_hash Num (of_int Num))

// Chaining: int32 arithmetic returns int32 — chain further
(neg (neg (of_int Num)))
(abs (neg (of_int Num)))
(succ (pred (of_int Num)))
(add (succ (of_int Num)) (pred (of_int Num)))
(mul (abs (of_int Num)) one)
(logand (shift_left (of_int Num) Num) (shift_right (of_int Num) Num))
(lognot (logxor (of_int Num) (of_int Num)))

// of_int output (int32) used in further int32 ops
(neg (of_int Num))
(succ (of_int Num))
(add (of_int Num) zero)
(equal (of_int Num) zero)
(compare (of_int Num) zero)
(min (of_int Num) zero)
(to_int (of_int Num))
(to_string (of_int Num))
(to_float (of_int Num))

// to_int returns plain int: use in normal int operations
(= (to_int (of_int Num)) Num)
(succ (to_int (of_int Num)))
(+ (to_int (of_int Num)) Num)
(to_int (succ (of_int Num)))
(to_int (add (of_int Num) one))

// to_float returns float: use in float arithmetic
(+. (to_float (of_int Num)) Flt)
(= (to_float (of_int Num)) Flt)

// to_string returns string
(= (to_string (of_int Num)) Str)
(^ (to_string (of_int Num)) Str)
(^ (to_string zero) (to_string one))

// compare returns int
(= (compare (of_int Num) (of_int Num)) Num)
(succ (compare (of_int Num) (of_int Num)))
(< (compare (of_int Num) (of_int Num)) Num)

// equal returns bool
(= (equal (of_int Num) (of_int Num)) true)
(not (equal (of_int Num) (of_int Num)))
(equal (min (of_int Num) (of_int Num)) (of_int Num))

// min/max return int32: chain
(to_int (min (of_int Num) (of_int Num)))
(to_int (max (of_int Num) (of_int Num)))
(equal (min (of_int Num) (of_int Num)) zero)
(succ (min (of_int Num) (of_int Num)))
(neg (max (of_int Num) (of_int Num)))

// hash returns int
(= (hash (of_int Num)) Num)
(succ (hash (of_int Num)))

// Invalid: int32 values used in plain int operations and vice versa
(+ (of_int Num) Num)
(succ (of_int Num))
(abs (of_int Num))
(add Num Num)
(add (of_int Num) Num)
(to_int Num)
(to_string (of_int Num) Num)
(equal (of_int Num) Num)
(compare (of_int Num) Num)
