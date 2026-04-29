// 0-basics.types, 1-comparison.types, 4-arith.types, 7-str.types, 11-pair.types, 38-float-mod.types

// Float constants
zero
one
minus_one
nan
infinity
neg_infinity
pi
max_float
min_float
epsilon

// Predicates: float -> bool
(is_finite Flt)
(is_infinite Flt)
(is_nan Flt)
(is_integer Flt)
(is_finite infinity)
(is_infinite infinity)
(is_nan nan)
(sign_bit Flt)
(sign_bit minus_one)
(sign_bit zero)

// Conversions
(of_int Num)
(to_int Flt)
(of_string Str)
(of_string_opt Str)
(to_string Flt)
(to_string zero)
(to_string pi)

// Rounding
(round Flt)
(floor Flt)
(ceil Flt)
(trunc Flt)

// Math functions
(sqrt Flt)
(cbrt Flt)
(exp Flt)
(exp2 Flt)
(log Flt)
(log2 Flt)
(log10 Flt)
(expm1 Flt)
(log1p Flt)
(cos Flt)
(sin Flt)
(tan Flt)
(acos Flt)
(asin Flt)
(atan Flt)
(atan2 Flt Flt)
(hypot Flt Flt)
(cosh Flt)
(sinh Flt)
(tanh Flt)
(acosh Flt)
(asinh Flt)
(atanh Flt)
(erf Flt)
(erfc Flt)

// Binary arithmetic
(add Flt Flt)
(sub Flt Flt)
(mul Flt Flt)
(div Flt Flt)
(rem Flt Flt)
(abs Flt)
(neg Flt)
(succ Flt)
(pred Flt)
(next_after Flt Flt)
(copy_sign Flt Flt)
(mod_float Flt Flt)

// Min/max
(min Flt Flt)
(max Flt Flt)
(min_num Flt Flt)
(max_num Flt Flt)
(min_max Flt Flt)
(min_max_num Flt Flt)

// Pairs from modf/frexp/min_max
(modf Flt)
(frexp Flt)
(fst (modf Flt))
(snd (modf Flt))
(fst (frexp Flt))
(snd (frexp Flt))
(fst (min_max Flt Flt))
(snd (min_max Flt Flt))

// compare/equal
(compare Flt Flt)
(equal Flt Flt)

// hash
(hash Flt)
(seeded_hash Num Flt)

// Float.Array submodule
(Array.make Num Flt)
(Array.create Num)
(Array.init Num sqrt)
(Array.init Num (fun i1 -> of_int i1))
(Array.length (Array.make Num Flt))
(Array.get (Array.make Num Flt) Num)
(Array.append (Array.make Num Flt) (Array.make Num Flt))
(Array.copy (Array.make Num Flt))
(Array.map sqrt (Array.make Num Flt))
(Array.map abs (Array.make Num Flt))
(Array.for_all is_finite (Array.make Num Flt))
(Array.for_all (fun x1 -> (= x1 Flt)) (Array.make Num Flt))
(Array.exists is_nan (Array.make Num Flt))
(Array.mem Flt (Array.make Num Flt))
(Array.fold_left add Flt (Array.make Num Flt))
(Array.equal (Array.make Num Flt) (Array.make Num Flt))

// Chaining: unary ops return float, chain them
(abs (neg Flt))
(neg (abs Flt))
(sqrt (abs Flt))
(round (abs Flt))
(floor (ceil Flt))
(ceil (floor Flt))
(trunc (round Flt))
(exp (log Flt))
(log (exp Flt))
(abs (sub Flt Flt))
(succ (pred Flt))
(pred (succ Flt))

// Binary ops on unary results
(add (sqrt Flt) (exp Flt))
(mul (sin Flt) (cos Flt))
(div (exp Flt) (exp Flt))
(min (abs Flt) (abs Flt))
(max (floor Flt) (ceil Flt))
(hypot (sin Flt) (cos Flt))
(atan2 (sin Flt) (cos Flt))

// Predicate chains
(is_finite (abs Flt))
(is_nan (sqrt (neg Flt)))
(is_infinite (div one zero))
(sign_bit (neg Flt))
(sign_bit (abs Flt))

// Conversions chain
(of_int (to_int Flt))
(to_string (of_int Num))
(of_string (to_string Flt))
(sqrt (of_int Num))
(add (of_int Num) Flt)

// compare returns int: use in arithmetic
(= (compare Flt Flt) Num)
(< (compare Flt Flt) Num)
(succ (compare Flt Flt))

// equal returns bool
(= (equal Flt Flt) true)
(not (equal Flt Flt))

// hash returns int
(= (hash Flt) Num)
(succ (hash Flt))
(seeded_hash (hash Flt) Flt)

// modf/frexp pair outputs
(add (fst (modf Flt)) (snd (modf Flt)))
(ldexp Flt (snd (frexp Flt)))
(add (fst (min_max Flt Flt)) (snd (min_max Flt Flt)))

// Float.Array chaining
(= (Array.length (Array.make Num Flt)) Num)
(= (Array.get (Array.make Num Flt) Num) Flt)
(Array.map sqrt (Array.copy (Array.make Num Flt)))
(Array.length (Array.map abs (Array.make Num Flt)))
(= (Array.get (Array.map sqrt (Array.make Num Flt)) Num) Flt)
(Array.fold_left add (Array.get (Array.make Num Flt) Num) (Array.make Num Flt))
(= (Array.for_all is_finite (Array.make Num Flt)) true)

// Invalid
(sqrt Num)
(add Flt Num)
(of_int Flt)
(to_int Num)
(compare Flt Num)
(equal Flt Num)
(Array.make Num Num)
