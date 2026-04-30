// 0_basics.types, 1_comparison.types, 11_pair.types

(fst (Pair.make Num Str))
(fst (Pair.make Str Num))
(fst (Pair.make true Num))
(fst (Pair.make Char Flt))
(fst (Pair.make Num Num))

(snd (Pair.make Num Str))
(snd (Pair.make Str true))
(snd (Pair.make Num Num))
(snd (Pair.make Char Flt))

(fst (Pair.make (Pair.make Num Str) true))
(snd (Pair.make Num (Pair.make Str true)))
(fst (Pair.make (fst (Pair.make Num Str)) Char))
(snd (Pair.make Num (snd (Pair.make Str true))))

(= (fst (Pair.make Num Str)) Num)
(= (snd (Pair.make Num Str)) Str)

(fst Num)
(snd Str)
(fst true)

// fst returns the first component type: use in further calls
(= (fst (Pair.make Num Str)) Num)
(= (fst (Pair.make Str Num)) Str)
(= (fst (Pair.make true Char)) true)
(= (snd (Pair.make Num Str)) Str)
(= (snd (Pair.make Str true)) true)

// Use fst/snd output to build new pairs
(Pair.make (fst (Pair.make Num Str)) (fst (Pair.make Str Num)))
(Pair.make (snd (Pair.make Num Str)) (snd (Pair.make Char true)))
(Pair.make (fst (Pair.make Num Str)) (snd (Pair.make Char true)))

// Use fst/snd output as argument to fst/snd (nested pairs)
(fst (Pair.make (fst (Pair.make Num Str)) Char))
(snd (Pair.make Num (snd (Pair.make Str true))))
(fst (Pair.make (snd (Pair.make Num Str)) Num))
(snd (Pair.make Char (fst (Pair.make true Num))))

// fst/snd applied twice: unwrap two levels
(fst (fst (Pair.make (Pair.make Num Str) true)))
(snd (snd (Pair.make Num (Pair.make Str true))))
(fst (snd (Pair.make Num (Pair.make Str true))))
(snd (fst (Pair.make (Pair.make Num Str) true)))

// invalid: fst/snd output used at wrong type
(= (fst (Pair.make Num Str)) Str)
(= (snd (Pair.make Num Str)) Num)
(fst (Pair.make Num Str) Char)
