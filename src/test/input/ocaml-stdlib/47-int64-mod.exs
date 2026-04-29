// 0-basics.types, 1-comparison.types, 6-float.types, 7-str.types, 46-int32-mod.types, 47-int64-mod.types

// Constants (type int64)
zero
one
minus_one
max_int
min_int

// Constructing int64 values
(of_int Num)
(of_float Flt)
(of_string Str)
(of_int32 (Int32.of_int Num))
(of_int32 Int32.zero)

// Unary: int64 -> int64
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

// Binary: int64 -> int64 -> int64
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

// Shifts: int64 -> int -> int64
(shift_left (of_int Num) Num)
(shift_right (of_int Num) Num)
(shift_right_logical (of_int Num) Num)

// Conversions
(to_int zero)
(to_int (of_int Num))
(to_int32 zero)
(to_int32 (of_int Num))
(to_float zero)
(to_float (of_int Num))
(to_string zero)
(to_string (of_int Num))

// Comparison
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

// Chaining: int64 arithmetic returns int64
(neg (neg (of_int Num)))
(abs (neg (of_int Num)))
(succ (pred (of_int Num)))
(add (succ (of_int Num)) (pred (of_int Num)))
(mul (abs (of_int Num)) one)
(logand (shift_left (of_int Num) Num) (shift_right (of_int Num) Num))

// of_int output (int64) used in further int64 ops
(neg (of_int Num))
(add (of_int Num) zero)
(equal (of_int Num) zero)
(compare (of_int Num) zero)
(to_int (of_int Num))
(to_string (of_int Num))
(to_float (of_int Num))
(to_int32 (of_int Num))

// to_int returns plain int: use in int operations
(= (to_int (of_int Num)) Num)
(succ (to_int (of_int Num)))
(+ (to_int (of_int Num)) Num)
(to_int (succ (of_int Num)))
(to_int (add (of_int Num) one))

// to_int32 returns int32: use in int32 ops
(Int32.succ (to_int32 (of_int Num)))
(Int32.neg (to_int32 (of_int Num)))
(Int32.equal (to_int32 (of_int Num)) Int32.zero)
(Int32.to_int (to_int32 (of_int Num)))

// to_float returns float
(+. (to_float (of_int Num)) Flt)
(= (to_float (of_int Num)) Flt)

// to_string returns string
(= (to_string (of_int Num)) Str)
(^ (to_string (of_int Num)) Str)

// compare returns int
(= (compare (of_int Num) (of_int Num)) Num)
(succ (compare (of_int Num) (of_int Num)))

// equal returns bool
(= (equal (of_int Num) (of_int Num)) true)
(not (equal (of_int Num) (of_int Num)))

// min/max return int64: chain
(to_int (min (of_int Num) (of_int Num)))
(to_int (max (of_int Num) (of_int Num)))
(neg (min (of_int Num) (of_int Num)))
(equal (min (of_int Num) (of_int Num)) zero)

// hash returns int
(= (hash (of_int Num)) Num)
(succ (hash (of_int Num)))

// Invalid: int64 vs int / int32 mixups
(+ (of_int Num) Num)
(succ (of_int Num))
(add (of_int Num) Num)
(to_int Num)
(equal (of_int Num) Num)
(compare (of_int Num) Num)
(add (of_int Num) Int32.zero)
