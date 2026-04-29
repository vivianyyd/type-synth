// 0-basics.types, 4-arith.types, 6-float.types, 7-str.types, 24-bool-mod.types

// Basic bool operations (same as 2-boolean but from Bool module)
(not true)
(not false)
(&& true false)
(|| true false)
(logand true false)
(logor true false)
(logxor true false)
(logand true true)
(logor false false)
(logxor true true)

// equal and compare
(equal true true)
(equal false false)
(equal true false)
(compare true false)
(compare false true)
(compare true true)

// Conversions
(to_int true)
(to_int false)
(to_float true)
(to_float false)
(to_string true)
(to_string false)

// hash
(hash true)
(hash false)
(seeded_hash Num true)
(seeded_hash Num false)

// Chaining: not/&&/|| outputs are bools
(not (not true))
(not (&& true false))
(&& (not true) (not false))
(|| (&& true false) (not true))
(not (logand true false))
(logand (not true) (not false))
(logxor (logand true false) (logor true false))

// equal returns bool: use in further bool ops
(not (equal true false))
(&& (equal true true) (equal false false))
(|| (equal true false) (not false))

// compare returns int: use in arithmetic
(= (compare true false) Num)
(< (compare true false) Num)
(succ (compare true false))
(compare (compare true false) (compare false true))

// to_int returns int: use in arithmetic
(= (to_int true) Num)
(= (to_int false) Num)
(succ (to_int true))
(+ (to_int true) (to_int false))
(+ (to_int true) Num)
(compare (to_int true) (to_int false))

// to_float returns float: use in float arithmetic
(+. (to_float true) Flt)
(+. (to_float true) (to_float false))
(= (to_float false) Flt)

// to_string returns string: use in string operations
(= (to_string true) Str)
(^ (to_string true) Str)
(^ (to_string true) (to_string false))

// hash returns int
(= (hash true) Num)
(succ (hash false))
(+ (hash true) (hash false))
(compare (hash true) (hash false))

// seeded_hash returns int
(= (seeded_hash Num true) Num)
(succ (seeded_hash Num false))
(+ (seeded_hash Num true) (seeded_hash Num false))

// Invalid
(to_int Num)
(to_float Str)
(to_string Num)
(hash Num)
(equal true Num)
(compare true Num)
(logand Num false)
