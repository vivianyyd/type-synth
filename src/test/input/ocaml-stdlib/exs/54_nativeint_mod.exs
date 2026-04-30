// 0_basics.types, 1_comparison.types, 6_float.types, 7_str.types, 46_int32_mod.types, 54_nativeint_mod.types

// Constants (type nativeint)
Nativeint.zero
Nativeint.one
Nativeint.minus_one
Nativeint.max_int
Nativeint.min_int

// size: int constant
Nativeint.size

// Constructing nativeint values
(Nativeint.of_int Num)
(Nativeint.of_float Flt)
(Nativeint.of_string Str)
(Nativeint.of_int32 Int32.zero)
(Nativeint.of_int32 (Int32.of_int Num))

// Unary: nativeint -> nativeint
(Nativeint.neg Nativeint.zero)
(Nativeint.neg Nativeint.one)
(Nativeint.neg (Nativeint.of_int Num))
(Nativeint.abs (Nativeint.of_int Num))
(Nativeint.abs Nativeint.minus_one)
(Nativeint.succ Nativeint.zero)
(Nativeint.succ (Nativeint.of_int Num))
(Nativeint.pred Nativeint.one)
(Nativeint.pred (Nativeint.of_int Num))
(Nativeint.lognot (Nativeint.of_int Num))

// Binary: nativeint -> nativeint -> nativeint
(Nativeint.add Nativeint.zero Nativeint.one)
(Nativeint.add (Nativeint.of_int Num) (Nativeint.of_int Num))
(Nativeint.sub Nativeint.one Nativeint.zero)
(Nativeint.sub (Nativeint.of_int Num) (Nativeint.of_int Num))
(Nativeint.mul Nativeint.zero Nativeint.one)
(Nativeint.mul (Nativeint.of_int Num) (Nativeint.of_int Num))
(Nativeint.div Nativeint.one Nativeint.one)
(Nativeint.div (Nativeint.of_int Num) Nativeint.one)
(Nativeint.rem (Nativeint.of_int Num) Nativeint.one)
(Nativeint.unsigned_div (Nativeint.of_int Num) Nativeint.one)
(Nativeint.unsigned_rem (Nativeint.of_int Num) Nativeint.one)
(Nativeint.logand (Nativeint.of_int Num) (Nativeint.of_int Num))
(Nativeint.logor (Nativeint.of_int Num) (Nativeint.of_int Num))
(Nativeint.logxor (Nativeint.of_int Num) (Nativeint.of_int Num))

// Shifts: nativeint -> int -> nativeint
(Nativeint.shift_left (Nativeint.of_int Num) Num)
(Nativeint.shift_right (Nativeint.of_int Num) Num)
(Nativeint.shift_right_logical (Nativeint.of_int Num) Num)

// Conversions
(Nativeint.to_int Nativeint.zero)
(Nativeint.to_int (Nativeint.of_int Num))
(Nativeint.to_int32 Nativeint.zero)
(Nativeint.to_int32 (Nativeint.of_int Num))
(Nativeint.to_float Nativeint.zero)
(Nativeint.to_float (Nativeint.of_int Num))
(Nativeint.to_string Nativeint.zero)
(Nativeint.to_string (Nativeint.of_int Num))

// Comparison
(Nativeint.compare Nativeint.zero Nativeint.one)
(Nativeint.compare (Nativeint.of_int Num) (Nativeint.of_int Num))
(Nativeint.unsigned_compare (Nativeint.of_int Num) (Nativeint.of_int Num))
(Nativeint.equal Nativeint.zero Nativeint.one)
(Nativeint.equal (Nativeint.of_int Num) (Nativeint.of_int Num))
(Nativeint.min Nativeint.zero Nativeint.one)
(Nativeint.max Nativeint.zero Nativeint.one)
(Nativeint.min (Nativeint.of_int Num) (Nativeint.of_int Num))
(Nativeint.max (Nativeint.of_int Num) (Nativeint.of_int Num))

// hash
(Nativeint.hash (Nativeint.of_int Num))
(Nativeint.seeded_hash Num (Nativeint.of_int Num))

// Chaining: nativeint arithmetic returns nativeint
(Nativeint.neg (Nativeint.neg (Nativeint.of_int Num)))
(Nativeint.abs (Nativeint.neg (Nativeint.of_int Num)))
(Nativeint.succ (Nativeint.pred (Nativeint.of_int Num)))
(Nativeint.add (Nativeint.succ (Nativeint.of_int Num)) (Nativeint.pred (Nativeint.of_int Num)))
(Nativeint.mul (Nativeint.abs (Nativeint.of_int Num)) Nativeint.one)
(Nativeint.logand (Nativeint.shift_left (Nativeint.of_int Num) Num) (Nativeint.shift_right (Nativeint.of_int Num) Num))

// size is int — use in int operations
((=) Nativeint.size Num)
(Nativeint.succ Nativeint.size)
((<) Nativeint.size Num)
(Nativeint.shift_left (Nativeint.of_int Num) Nativeint.size)

// to_int returns plain int
((=) (Nativeint.to_int (Nativeint.of_int Num)) Num)
(Nativeint.succ (Nativeint.to_int (Nativeint.of_int Num)))
((+) (Nativeint.to_int (Nativeint.of_int Num)) Num)
(Nativeint.shift_left (Nativeint.of_int Num) (Nativeint.to_int (Nativeint.of_int Num)))

// to_int32 returns int32
(Int32.succ (Nativeint.to_int32 (Nativeint.of_int Num)))
(Int32.equal (Nativeint.to_int32 (Nativeint.of_int Num)) Int32.zero)
(Int32.to_int (Nativeint.to_int32 (Nativeint.of_int Num)))

// to_float returns float
((+.) (Nativeint.to_float (Nativeint.of_int Num)) Flt)
((=) (Nativeint.to_float (Nativeint.of_int Num)) Flt)

// to_string returns string
((=) (Nativeint.to_string (Nativeint.of_int Num)) Str)
((^) (Nativeint.to_string (Nativeint.of_int Num)) Str)

// compare returns int
((=) (Nativeint.compare (Nativeint.of_int Num) (Nativeint.of_int Num)) Num)
(Nativeint.succ (Nativeint.compare (Nativeint.of_int Num) (Nativeint.of_int Num)))

// equal returns bool
((=) (Nativeint.equal (Nativeint.of_int Num) (Nativeint.of_int Num)) true)
(not (Nativeint.equal (Nativeint.of_int Num) (Nativeint.of_int Num)))

// min/max return nativeint
(Nativeint.to_int (Nativeint.min (Nativeint.of_int Num) (Nativeint.of_int Num)))
(Nativeint.neg (Nativeint.max (Nativeint.of_int Num) (Nativeint.of_int Num)))
(Nativeint.equal (Nativeint.min (Nativeint.of_int Num) (Nativeint.of_int Num)) Nativeint.zero)

// hash returns int
((=) (Nativeint.hash (Nativeint.of_int Num)) Num)
(Nativeint.succ (Nativeint.hash (Nativeint.of_int Num)))

// Invalid: nativeint vs plain int mixups
((+) (Nativeint.of_int Num) Num)
(Nativeint.succ (Nativeint.of_int Num))
(Nativeint.add (Nativeint.of_int Num) Num)
(Nativeint.to_int Num)
(Nativeint.equal (Nativeint.of_int Num) Num)
(Nativeint.shift_left (Nativeint.of_int Num) (Nativeint.of_int Num))
