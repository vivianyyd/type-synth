// 0_basics.types, 4_arith.types, 6_float.types, 7_str.types, 24_bool_mod.types

// Basic bool operations (same as 2-boolean but from Bool module)
(Bool.not true)
(Bool.not false)
((&&) true false)
((||) true false)
(Bool.logand true false)
(Bool.logor true false)
(Bool.logxor true false)
(Bool.logand true true)
(Bool.logor false false)
(Bool.logxor true true)

// equal and compare
(Bool.equal true true)
(Bool.equal false false)
(Bool.equal true false)
(Bool.compare true false)
(Bool.compare false true)
(Bool.compare true true)

// Conversions
(Bool.to_int true)
(Bool.to_int false)
(Bool.to_float true)
(Bool.to_float false)
(Bool.to_string true)
(Bool.to_string false)

// hash
(Bool.hash true)
(Bool.hash false)
(Bool.seeded_hash Num true)
(Bool.seeded_hash Num false)

// Chaining: not/&&/|| outputs are bools
(Bool.not (Bool.not true))
(Bool.not ((&&) true false))
((&&) (Bool.not true) (Bool.not false))
((||) ((&&) true false) (Bool.not true))
(Bool.not (Bool.logand true false))
(Bool.logand (Bool.not true) (Bool.not false))
(Bool.logxor (Bool.logand true false) (Bool.logor true false))

// equal returns bool: use in further bool ops
(Bool.not (Bool.equal true false))
((&&) (Bool.equal true true) (Bool.equal false false))
((||) (Bool.equal true false) (Bool.not false))

// compare returns int: use in arithmetic
((=) (Bool.compare true false) Num)
((<) (Bool.compare true false) Num)
(succ (Bool.compare true false))
(Bool.compare (Bool.compare true false) (Bool.compare false true))

// to_int returns int: use in arithmetic
((=) (Bool.to_int true) Num)
((=) (Bool.to_int false) Num)
(succ (Bool.to_int true))
((+) (Bool.to_int true) (Bool.to_int false))
((+) (Bool.to_int true) Num)
(Bool.compare (Bool.to_int true) (Bool.to_int false))

// to_float returns float: use in float arithmetic
((+.) (Bool.to_float true) Flt)
((+.) (Bool.to_float true) (Bool.to_float false))
((=) (Bool.to_float false) Flt)

// to_string returns string: use in string operations
((=) (Bool.to_string true) Str)
((^) (Bool.to_string true) Str)
((^) (Bool.to_string true) (Bool.to_string false))

// hash returns int
((=) (Bool.hash true) Num)
(succ (Bool.hash false))
((+) (Bool.hash true) (Bool.hash false))
(Bool.compare (Bool.hash true) (Bool.hash false))

// seeded_hash returns int
((=) (Bool.seeded_hash Num true) Num)
(succ (Bool.seeded_hash Num false))
((+) (Bool.seeded_hash Num true) (Bool.seeded_hash Num false))

// Invalid
(Bool.to_int Num)
(Bool.to_float Str)
(Bool.to_string Num)
(Bool.hash Num)
(Bool.equal true Num)
(Bool.compare true Num)
(Bool.logand Num false)
