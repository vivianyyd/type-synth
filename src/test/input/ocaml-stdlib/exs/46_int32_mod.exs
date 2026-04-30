// 0_basics.types, 1_comparison.types, 6_float.types, 7_str.types, 46_int32_mod.types

// Constants (type int32)
Int32.zero
Int32.one
Int32.minus_one
Int32.max_int
Int32.min_int

// Constructing int32 values
(Int32.of_int Num)
(Int32.of_float Flt)
(Int32.of_string Str)

// Unary: int32 -> int32
(Int32.neg Int32.zero)
(Int32.neg Int32.one)
(Int32.neg (Int32.of_int Num))
(Int32.abs (Int32.of_int Num))
(Int32.abs Int32.minus_one)
(Int32.succ Int32.zero)
(Int32.succ (Int32.of_int Num))
(Int32.pred Int32.one)
(Int32.pred (Int32.of_int Num))
(Int32.lognot (Int32.of_int Num))

// Binary: int32 -> int32 -> int32
(Int32.add Int32.zero Int32.one)
(Int32.add (Int32.of_int Num) (Int32.of_int Num))
(Int32.sub Int32.one Int32.zero)
(Int32.sub (Int32.of_int Num) (Int32.of_int Num))
(Int32.mul Int32.zero Int32.one)
(Int32.mul (Int32.of_int Num) (Int32.of_int Num))
(Int32.div Int32.one Int32.one)
(Int32.div (Int32.of_int Num) Int32.one)
(Int32.rem (Int32.of_int Num) Int32.one)
(Int32.unsigned_div (Int32.of_int Num) Int32.one)
(Int32.unsigned_rem (Int32.of_int Num) Int32.one)
(Int32.logand (Int32.of_int Num) (Int32.of_int Num))
(Int32.logor (Int32.of_int Num) (Int32.of_int Num))
(Int32.logxor (Int32.of_int Num) (Int32.of_int Num))

// Shifts: int32 -> int -> int32
(Int32.shift_left (Int32.of_int Num) Num)
(Int32.shift_right (Int32.of_int Num) Num)
(Int32.shift_right_logical (Int32.of_int Num) Num)

// Conversions to other types
(Int32.to_int Int32.zero)
(Int32.to_int Int32.one)
(Int32.to_int (Int32.of_int Num))
(Int32.to_float Int32.zero)
(Int32.to_float (Int32.of_int Num))
(Int32.to_string Int32.zero)
(Int32.to_string (Int32.of_int Num))

// Comparison: int32 -> int32 -> int / bool
(Int32.compare Int32.zero Int32.one)
(Int32.compare (Int32.of_int Num) (Int32.of_int Num))
(Int32.unsigned_compare (Int32.of_int Num) (Int32.of_int Num))
(Int32.equal Int32.zero Int32.one)
(Int32.equal (Int32.of_int Num) (Int32.of_int Num))
(Int32.min Int32.zero Int32.one)
(Int32.max Int32.zero Int32.one)
(Int32.min (Int32.of_int Num) (Int32.of_int Num))
(Int32.max (Int32.of_int Num) (Int32.of_int Num))

// hash
(Int32.hash (Int32.of_int Num))
(Int32.seeded_hash Num (Int32.of_int Num))

// Chaining: int32 arithmetic returns int32 — chain further
(Int32.neg (Int32.neg (Int32.of_int Num)))
(Int32.abs (Int32.neg (Int32.of_int Num)))
(Int32.succ (Int32.pred (Int32.of_int Num)))
(Int32.add (Int32.succ (Int32.of_int Num)) (Int32.pred (Int32.of_int Num)))
(Int32.mul (Int32.abs (Int32.of_int Num)) Int32.one)
(Int32.logand (Int32.shift_left (Int32.of_int Num) Num) (Int32.shift_right (Int32.of_int Num) Num))
(Int32.lognot (Int32.logxor (Int32.of_int Num) (Int32.of_int Num)))

// of_int output (int32) used in further int32 ops
(Int32.neg (Int32.of_int Num))
(Int32.succ (Int32.of_int Num))
(Int32.add (Int32.of_int Num) Int32.zero)
(Int32.equal (Int32.of_int Num) Int32.zero)
(Int32.compare (Int32.of_int Num) Int32.zero)
(Int32.min (Int32.of_int Num) Int32.zero)
(Int32.to_int (Int32.of_int Num))
(Int32.to_string (Int32.of_int Num))
(Int32.to_float (Int32.of_int Num))

// to_int returns plain int: use in normal int operations
((=) (Int32.to_int (Int32.of_int Num)) Num)
(Int32.succ (Int32.to_int (Int32.of_int Num)))
((+) (Int32.to_int (Int32.of_int Num)) Num)
(Int32.to_int (Int32.succ (Int32.of_int Num)))
(Int32.to_int (Int32.add (Int32.of_int Num) Int32.one))

// to_float returns float: use in float arithmetic
((+.) (Int32.to_float (Int32.of_int Num)) Flt)
((=) (Int32.to_float (Int32.of_int Num)) Flt)

// to_string returns string
((=) (Int32.to_string (Int32.of_int Num)) Str)
((^) (Int32.to_string (Int32.of_int Num)) Str)
((^) (Int32.to_string Int32.zero) (Int32.to_string Int32.one))

// compare returns int
((=) (Int32.compare (Int32.of_int Num) (Int32.of_int Num)) Num)
(Int32.succ (Int32.compare (Int32.of_int Num) (Int32.of_int Num)))
((<) (Int32.compare (Int32.of_int Num) (Int32.of_int Num)) Num)

// equal returns bool
((=) (Int32.equal (Int32.of_int Num) (Int32.of_int Num)) true)
(not (Int32.equal (Int32.of_int Num) (Int32.of_int Num)))
(Int32.equal (Int32.min (Int32.of_int Num) (Int32.of_int Num)) (Int32.of_int Num))

// min/max return int32: chain
(Int32.to_int (Int32.min (Int32.of_int Num) (Int32.of_int Num)))
(Int32.to_int (Int32.max (Int32.of_int Num) (Int32.of_int Num)))
(Int32.equal (Int32.min (Int32.of_int Num) (Int32.of_int Num)) Int32.zero)
(Int32.succ (Int32.min (Int32.of_int Num) (Int32.of_int Num)))
(Int32.neg (Int32.max (Int32.of_int Num) (Int32.of_int Num)))

// hash returns int
((=) (Int32.hash (Int32.of_int Num)) Num)
(Int32.succ (Int32.hash (Int32.of_int Num)))

// Invalid: int32 values used in plain int operations and vice versa
((+) (Int32.of_int Num) Num)
(Int32.succ (Int32.of_int Num))
(Int32.abs (Int32.of_int Num))
(Int32.add Num Num)
(Int32.add (Int32.of_int Num) Num)
(Int32.to_int Num)
(Int32.to_string (Int32.of_int Num) Num)
(Int32.equal (Int32.of_int Num) Num)
(Int32.compare (Int32.of_int Num) Num)
