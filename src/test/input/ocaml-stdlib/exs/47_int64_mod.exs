// 0_basics.types, 1_comparison.types, 6_float.types, 7_str.types, 46_int32_mod.types, 47_int64_mod.types

// Constants (type int64)
Int64.zero
Int64.one
Int64.minus_one
Int64.max_int
Int64.min_int

// Constructing int64 values
(Int64.of_int Num)
(Int64.of_float Flt)
(Int64.of_string Str)
(Int64.of_int32 (Int32.of_int Num))
(Int64.of_int32 Int32.zero)

// Unary: int64 -> int64
(Int64.neg Int64.zero)
(Int64.neg Int64.one)
(Int64.neg (Int64.of_int Num))
(Int64.abs (Int64.of_int Num))
(Int64.abs Int64.minus_one)
(Int64.succ Int64.zero)
(Int64.succ (Int64.of_int Num))
(Int64.pred Int64.one)
(Int64.pred (Int64.of_int Num))
(Int64.lognot (Int64.of_int Num))

// Binary: int64 -> int64 -> int64
(Int64.add Int64.zero Int64.one)
(Int64.add (Int64.of_int Num) (Int64.of_int Num))
(Int64.sub Int64.one Int64.zero)
(Int64.sub (Int64.of_int Num) (Int64.of_int Num))
(Int64.mul Int64.zero Int64.one)
(Int64.mul (Int64.of_int Num) (Int64.of_int Num))
(Int64.div Int64.one Int64.one)
(Int64.div (Int64.of_int Num) Int64.one)
(Int64.rem (Int64.of_int Num) Int64.one)
(Int64.unsigned_div (Int64.of_int Num) Int64.one)
(Int64.unsigned_rem (Int64.of_int Num) Int64.one)
(Int64.logand (Int64.of_int Num) (Int64.of_int Num))
(Int64.logor (Int64.of_int Num) (Int64.of_int Num))
(Int64.logxor (Int64.of_int Num) (Int64.of_int Num))

// Shifts: int64 -> int -> int64
(Int64.shift_left (Int64.of_int Num) Num)
(Int64.shift_right (Int64.of_int Num) Num)
(Int64.shift_right_logical (Int64.of_int Num) Num)

// Conversions
(Int64.to_int Int64.zero)
(Int64.to_int (Int64.of_int Num))
(Int64.to_int32 Int64.zero)
(Int64.to_int32 (Int64.of_int Num))
(Int64.to_float Int64.zero)
(Int64.to_float (Int64.of_int Num))
(Int64.to_string Int64.zero)
(Int64.to_string (Int64.of_int Num))

// Comparison
(Int64.compare Int64.zero Int64.one)
(Int64.compare (Int64.of_int Num) (Int64.of_int Num))
(Int64.unsigned_compare (Int64.of_int Num) (Int64.of_int Num))
(Int64.equal Int64.zero Int64.one)
(Int64.equal (Int64.of_int Num) (Int64.of_int Num))
(Int64.min Int64.zero Int64.one)
(Int64.max Int64.zero Int64.one)
(Int64.min (Int64.of_int Num) (Int64.of_int Num))
(Int64.max (Int64.of_int Num) (Int64.of_int Num))

// hash
(Int64.hash (Int64.of_int Num))
(Int64.seeded_hash Num (Int64.of_int Num))

// Chaining: int64 arithmetic returns int64
(Int64.neg (Int64.neg (Int64.of_int Num)))
(Int64.abs (Int64.neg (Int64.of_int Num)))
(Int64.succ (Int64.pred (Int64.of_int Num)))
(Int64.add (Int64.succ (Int64.of_int Num)) (Int64.pred (Int64.of_int Num)))
(Int64.mul (Int64.abs (Int64.of_int Num)) Int64.one)
(Int64.logand (Int64.shift_left (Int64.of_int Num) Num) (Int64.shift_right (Int64.of_int Num) Num))

// of_int output (int64) used in further int64 ops
(Int64.neg (Int64.of_int Num))
(Int64.add (Int64.of_int Num) Int64.zero)
(Int64.equal (Int64.of_int Num) Int64.zero)
(Int64.compare (Int64.of_int Num) Int64.zero)
(Int64.to_int (Int64.of_int Num))
(Int64.to_string (Int64.of_int Num))
(Int64.to_float (Int64.of_int Num))
(Int64.to_int32 (Int64.of_int Num))

// to_int returns plain int: use in int operations
((=) (Int64.to_int (Int64.of_int Num)) Num)
(Int64.succ (Int64.to_int (Int64.of_int Num)))
((+) (Int64.to_int (Int64.of_int Num)) Num)
(Int64.to_int (Int64.succ (Int64.of_int Num)))
(Int64.to_int (Int64.add (Int64.of_int Num) Int64.one))

// to_int32 returns int32: use in int32 ops
(Int32.succ (Int64.to_int32 (Int64.of_int Num)))
(Int32.neg (Int64.to_int32 (Int64.of_int Num)))
(Int32.equal (Int64.to_int32 (Int64.of_int Num)) Int32.zero)
(Int32.to_int (Int64.to_int32 (Int64.of_int Num)))

// to_float returns float
((+.) (Int64.to_float (Int64.of_int Num)) Flt)
((=) (Int64.to_float (Int64.of_int Num)) Flt)

// to_string returns string
((=) (Int64.to_string (Int64.of_int Num)) Str)
((^) (Int64.to_string (Int64.of_int Num)) Str)

// compare returns int
((=) (Int64.compare (Int64.of_int Num) (Int64.of_int Num)) Num)
(Int64.succ (Int64.compare (Int64.of_int Num) (Int64.of_int Num)))

// equal returns bool
((=) (Int64.equal (Int64.of_int Num) (Int64.of_int Num)) true)
(not (Int64.equal (Int64.of_int Num) (Int64.of_int Num)))

// min/max return int64: chain
(Int64.to_int (Int64.min (Int64.of_int Num) (Int64.of_int Num)))
(Int64.to_int (Int64.max (Int64.of_int Num) (Int64.of_int Num)))
(Int64.neg (Int64.min (Int64.of_int Num) (Int64.of_int Num)))
(Int64.equal (Int64.min (Int64.of_int Num) (Int64.of_int Num)) Int64.zero)

// hash returns int
((=) (Int64.hash (Int64.of_int Num)) Num)
(Int64.succ (Int64.hash (Int64.of_int Num)))

// Invalid: int64 vs int / int32 mixups
((+) (Int64.of_int Num) Num)
(Int64.succ (Int64.of_int Num))
(Int64.add (Int64.of_int Num) Num)
(Int64.to_int Num)
(Int64.equal (Int64.of_int Num) Num)
(Int64.compare (Int64.of_int Num) Num)
(Int64.add (Int64.of_int Num) Int32.zero)
