// 0_basics.types, 1_comparison.types, 2_boolean.types, 4_arith.types, 80_seq_core_mod.types

// Seq.empty, polymorphic, at several element types and with every function
Seq.empty
(Seq.is_empty Seq.empty)
(Seq.length Seq.empty)
(Seq.for_all ((=) Num) Seq.empty)
(Seq.for_all ((=) Str) Seq.empty)
(Seq.cons Num Seq.empty)
(Seq.cons Str Seq.empty)
(Seq.cons Char Seq.empty)
(Seq.cons true Seq.empty)

// Seq.return: a sequence of any one value
(Seq.return Num)
(Seq.return Str)
(Seq.return Char)
(Seq.return true)
(Seq.is_empty (Seq.return Num))
(Seq.is_empty (Seq.return Str))
(Seq.length (Seq.return Char))

// Its result is a sequence, not the element
(succ (Seq.return Num))
(not (Seq.return true))
((=) (Seq.return Num) Num)

// Seq.cons: the element and the sequence share their type, the sequence last
(Seq.cons Num (Seq.return Num))
(Seq.cons Str (Seq.return Str))
(Seq.cons Char (Seq.cons Char Seq.empty))
(Seq.cons Num (Seq.return Str))
(Seq.cons Str (Seq.return Num))
(Seq.cons true (Seq.return Num))
(Seq.cons Num)
(Seq.cons Num Num)
(Seq.cons Num Str)

// Its result is a sequence of the same elements
(Seq.is_empty (Seq.cons Num Seq.empty))
(Seq.length (Seq.cons Num (Seq.return Num)))
(succ (Seq.cons Num Seq.empty))

// Seq.for_all: the predicate's argument is the sequence's element. These are what give Seq its
// parameter: with Seq.t at no parameter the two negatives below type-check.
(Seq.for_all ((=) Num) (Seq.return Num))
(Seq.for_all ((=) Str) (Seq.return Str))
(Seq.for_all ((=) Char) (Seq.return Char))
(Seq.for_all not (Seq.return true))
(Seq.for_all ((<) Num) (Seq.return Num))
(Seq.for_all ((=) Num) (Seq.cons Num (Seq.return Num)))
(Seq.for_all ((=) Num) (Seq.return Str))
(Seq.for_all ((=) Str) (Seq.return Num))
(Seq.for_all ((=) Num) (Seq.return Char))
(Seq.for_all not (Seq.return Num))
(Seq.for_all ((=) Num) (Seq.cons Str Seq.empty))
(Seq.for_all ((=) Str) (Seq.cons Num (Seq.return Num)))

// Its first argument is a predicate, its second a sequence
(Seq.for_all ((=) Num))
(Seq.for_all succ)
(Seq.for_all Num)
(Seq.for_all (Seq.return Num))
(Seq.for_all ((=) Num) Num)
(Seq.for_all ((=) Num) true)

// Results: for_all and is_empty are bool, length is int
(not (Seq.for_all ((=) Num) (Seq.return Num)))
((&&) (Seq.for_all ((=) Num) Seq.empty) true)
(succ (Seq.for_all ((=) Num) (Seq.return Num)))
(not (Seq.is_empty Seq.empty))
((||) (Seq.is_empty Seq.empty) false)
(succ (Seq.is_empty Seq.empty))
(succ (Seq.length Seq.empty))
((+) (Seq.length (Seq.return Num)) Num)
(not (Seq.length Seq.empty))
((=) (Seq.length Seq.empty) Str)

// Arguments that are not sequences at all
(Seq.is_empty Num)
(Seq.is_empty Str)
(Seq.length true)
(Seq.length Char)
