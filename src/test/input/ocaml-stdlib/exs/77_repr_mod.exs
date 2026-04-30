// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 77_repr_mod.types

// phys_equal: 'a -> 'a -> bool
(Repr.phys_equal Num Num)
(Repr.phys_equal Str Str)
(Repr.phys_equal true true)

// equal: 'a -> 'a -> bool
(Repr.equal Num Num)
(Repr.equal Str Str)
(Repr.equal true true)
(Repr.equal Char Char)

// compare: 'a -> 'a -> int
(Repr.compare Num Num)
(Repr.compare Str Str)
(Repr.compare true false)

// min: 'a -> 'a -> 'a
(Repr.min Num Num)
(Repr.min Str Str)
(Repr.min true false)

// max: 'a -> 'a -> 'a
(Repr.max Num Num)
(Repr.max Str Str)
(Repr.max true false)

// Chaining: equal/phys_equal return bool
((=) (Repr.equal Num Num) true)
(not (Repr.equal Num Num))
((&&) (Repr.equal Num Num) (Repr.phys_equal Num Num))
((||) (Repr.equal Str Str) (Repr.equal Num Num))
(not (Repr.phys_equal Str Str))

// compare returns int
((=) (Repr.compare Num Num) Num)
(succ (Repr.compare Num Num))
((<) (Repr.compare Num Num) Num)
((+) (Repr.compare Num Num) (Repr.compare Str Str))

// min/max return same type as inputs
((=) (Repr.min Num Num) Num)
(succ (Repr.min Num Num))
((^) (Repr.min Str Str) Str)
(not (Repr.min true false))
(Repr.min (Repr.min Num Num) Num)
(Repr.max (Repr.min Num Num) (Repr.max Num Num))
((=) (Repr.min Num Num) (Repr.max Num Num))
(Repr.compare (Repr.min Num Num) (Repr.max Num Num))
(Repr.equal (Repr.min Num Num) (Repr.max Num Num))

// Invalid
(Repr.phys_equal Num Str)
(Repr.equal Num Str)
(Repr.compare Num Str)
(Repr.min Num Str)
(Repr.max Num Str)
(succ (Repr.equal Num Num))
(not (Repr.compare Num Num))
