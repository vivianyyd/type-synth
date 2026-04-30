// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 11_pair.types, 38_float_mod.types

// Float constants
Float.zero
Float.one
Float.minus_one
Float.nan
Float.infinity
Float.neg_infinity
Float.pi
Float.max_float
Float.min_float
Float.epsilon

// Predicates: float -> bool
(Float.is_finite Flt)
(Float.is_infinite Flt)
(Float.is_nan Flt)
(Float.is_integer Flt)
(Float.is_finite Float.infinity)
(Float.is_infinite Float.infinity)
(Float.is_nan Float.nan)
(Float.sign_bit Flt)
(Float.sign_bit Float.minus_one)
(Float.sign_bit Float.zero)

// Conversions
(Float.of_int Num)
(Float.to_int Flt)
(Float.of_string Str)
(Float.of_string_opt Str)
(Float.to_string Flt)
(Float.to_string Float.zero)
(Float.to_string Float.pi)

// Rounding
(Float.round Flt)
(Float.floor Flt)
(Float.ceil Flt)
(Float.trunc Flt)

// Math functions
(Float.sqrt Flt)
(Float.cbrt Flt)
(Float.exp Flt)
(Float.exp2 Flt)
(Float.log Flt)
(Float.log2 Flt)
(Float.log10 Flt)
(Float.expm1 Flt)
(Float.log1p Flt)
(Float.cos Flt)
(Float.sin Flt)
(Float.tan Flt)
(Float.acos Flt)
(Float.asin Flt)
(Float.atan Flt)
(Float.atan2 Flt Flt)
(Float.hypot Flt Flt)
(Float.cosh Flt)
(Float.sinh Flt)
(Float.tanh Flt)
(Float.acosh Flt)
(Float.asinh Flt)
(Float.atanh Flt)
(Float.erf Flt)
(Float.erfc Flt)

// Binary arithmetic
(Float.add Flt Flt)
(Float.sub Flt Flt)
(Float.mul Flt Flt)
(Float.div Flt Flt)
(Float.rem Flt Flt)
(Float.abs Flt)
(Float.neg Flt)
(Float.succ Flt)
(Float.pred Flt)
(Float.next_after Flt Flt)
(Float.copy_sign Flt Flt)
(Float.mod_float Flt Flt)

// Min/max
(Float.min Flt Flt)
(Float.max Flt Flt)
(Float.min_num Flt Flt)
(Float.max_num Flt Flt)
(Float.min_max Flt Flt)
(Float.min_max_num Flt Flt)

// Pairs from modf/frexp/min_max
(Float.modf Flt)
(Float.frexp Flt)
(fst (Float.modf Flt))
(snd (Float.modf Flt))
(fst (Float.frexp Flt))
(snd (Float.frexp Flt))
(fst (Float.min_max Flt Flt))
(snd (Float.min_max Flt Flt))

// compare/equal
(Float.compare Flt Flt)
(Float.equal Flt Flt)

// hash
(Float.hash Flt)
(Float.seeded_hash Num Flt)

// Float.Array submodule
(Float.Array.make Num Flt)
(Float.Array.create Num)
(Float.Array.init Num Float.sqrt)
(Float.Array.init Num (fun i1 -> Float.of_int i1))
(Float.Array.length (Float.Array.make Num Flt))
(Float.Array.get (Float.Array.make Num Flt) Num)
(Float.Array.append (Float.Array.make Num Flt) (Float.Array.make Num Flt))
(Float.Array.copy (Float.Array.make Num Flt))
(Float.Array.map Float.sqrt (Float.Array.make Num Flt))
(Float.Array.map Float.abs (Float.Array.make Num Flt))
(Float.Array.for_all Float.is_finite (Float.Array.make Num Flt))
(Float.Array.for_all (fun x1 -> ((=) x1 Flt)) (Float.Array.make Num Flt))
(Float.Array.exists Float.is_nan (Float.Array.make Num Flt))
(Float.Array.mem Flt (Float.Array.make Num Flt))
(Float.Array.fold_left Float.add Flt (Float.Array.make Num Flt))
(Float.Array.equal (Float.Array.make Num Flt) (Float.Array.make Num Flt))

// Chaining: unary ops return float, chain them
(Float.abs (Float.neg Flt))
(Float.neg (Float.abs Flt))
(Float.sqrt (Float.abs Flt))
(Float.round (Float.abs Flt))
(Float.floor (Float.ceil Flt))
(Float.ceil (Float.floor Flt))
(Float.trunc (Float.round Flt))
(Float.exp (Float.log Flt))
(Float.log (Float.exp Flt))
(Float.abs (Float.sub Flt Flt))
(Float.succ (Float.pred Flt))
(Float.pred (Float.succ Flt))

// Binary ops on unary results
(Float.add (Float.sqrt Flt) (Float.exp Flt))
(Float.mul (Float.sin Flt) (Float.cos Flt))
(Float.div (Float.exp Flt) (Float.exp Flt))
(Float.min (Float.abs Flt) (Float.abs Flt))
(Float.max (Float.floor Flt) (Float.ceil Flt))
(Float.hypot (Float.sin Flt) (Float.cos Flt))
(Float.atan2 (Float.sin Flt) (Float.cos Flt))

// Predicate chains
(Float.is_finite (Float.abs Flt))
(Float.is_nan (Float.sqrt (Float.neg Flt)))
(Float.is_infinite (Float.div Float.one Float.zero))
(Float.sign_bit (Float.neg Flt))
(Float.sign_bit (Float.abs Flt))

// Conversions chain
(Float.of_int (Float.to_int Flt))
(Float.to_string (Float.of_int Num))
(Float.of_string (Float.to_string Flt))
(Float.sqrt (Float.of_int Num))
(Float.add (Float.of_int Num) Flt)

// compare returns int: use in arithmetic
((=) (Float.compare Flt Flt) Num)
((<) (Float.compare Flt Flt) Num)
(Float.succ (Float.compare Flt Flt))

// equal returns bool
((=) (Float.equal Flt Flt) true)
(not (Float.equal Flt Flt))

// hash returns int
((=) (Float.hash Flt) Num)
(Float.succ (Float.hash Flt))
(Float.seeded_hash (Float.hash Flt) Flt)

// modf/frexp pair outputs
(Float.add (fst (Float.modf Flt)) (snd (Float.modf Flt)))
(Float.ldexp Flt (snd (Float.frexp Flt)))
(Float.add (fst (Float.min_max Flt Flt)) (snd (Float.min_max Flt Flt)))

// Float.Array chaining
((=) (Float.Array.length (Float.Array.make Num Flt)) Num)
((=) (Float.Array.get (Float.Array.make Num Flt) Num) Flt)
(Float.Array.map Float.sqrt (Float.Array.copy (Float.Array.make Num Flt)))
(Float.Array.length (Float.Array.map Float.abs (Float.Array.make Num Flt)))
((=) (Float.Array.get (Float.Array.map Float.sqrt (Float.Array.make Num Flt)) Num) Flt)
(Float.Array.fold_left Float.add (Float.Array.get (Float.Array.make Num Flt) Num) (Float.Array.make Num Flt))
((=) (Float.Array.for_all Float.is_finite (Float.Array.make Num Flt)) true)

// Invalid
(Float.sqrt Num)
(Float.add Flt Num)
(Float.of_int Flt)
(Float.to_int Num)
(Float.compare Flt Num)
(Float.equal Flt Num)
(Float.Array.make Num Num)
