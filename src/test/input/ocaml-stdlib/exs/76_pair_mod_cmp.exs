// 0_basics.types, 1_comparison.types, 2_boolean.types, 4_arith.types, 7_str.types, 9_unit.types, 76_pair_mod.types

// Pair's iter, equal and compare, kept apart from 76_pair_mod.exs so that the groups that depend on
// pair_mod aren't blocked: with them, a round of pair_mod doesn't finish within the time limit.

// iter: ('a -> unit) -> ('b -> unit) -> 'a * 'b -> unit
(Pair.iter ignore ignore (Pair.make Num Str))
(Pair.iter ignore ignore (Pair.make true Num))
(ignore (Pair.iter ignore ignore (Pair.make Num Str)))
((=) Unit (Pair.iter ignore ignore (Pair.make Num Str)))
(succ (Pair.iter ignore ignore (Pair.make Num Str)))
(not (Pair.iter ignore ignore (Pair.make Num Str)))
(Pair.iter succ)
(Pair.iter ignore succ)
(Pair.iter ignore ignore Num)

// equal: ('a -> 'a -> bool) -> ('b -> 'b -> bool) -> 'a * 'b -> 'a * 'b -> bool
(Pair.equal (=) (=) (Pair.make Num Str) (Pair.make Num Str))
(Pair.equal (&&) (=) (Pair.make true Num) (Pair.make false Num))
(Pair.equal (=) (&&) (Pair.make Str true) (Pair.make Str false))
(not (Pair.equal (=) (=) (Pair.make Num Str) (Pair.make Num Str)))
(succ (Pair.equal (=) (=) (Pair.make Num Str) (Pair.make Num Str)))
(Pair.equal (=) (=) (Pair.make Num Str) (Pair.make Str Num))
(Pair.equal (=) (=) (Pair.make Num Str) (Pair.make Num true))
(Pair.equal (&&) (=) (Pair.make Num Num))
(Pair.equal (=) (&&) (Pair.make Num Num))
(Pair.equal (+))
(Pair.equal (=) (+))
(Pair.equal (=) (=) Num)

// compare: ('a -> 'a -> int) -> ('b -> 'b -> int) -> 'a * 'b -> 'a * 'b -> int
(Pair.compare compare compare (Pair.make Num Str) (Pair.make Num Str))
(Pair.compare (-) compare (Pair.make Num true) (Pair.make Num false))
(Pair.compare compare (-) (Pair.make Str Num) (Pair.make Str Num))
(succ (Pair.compare compare compare (Pair.make Num Str) (Pair.make Num Str)))
(not (Pair.compare compare compare (Pair.make Num Str) (Pair.make Num Str)))
(Pair.compare compare compare (Pair.make Num Str) (Pair.make Str Num))
(Pair.compare (-) compare (Pair.make Str Str))
(Pair.compare compare (-) (Pair.make Str Str))
(Pair.compare (=))
(Pair.compare compare (=))
(Pair.compare compare compare Num)

// Results compared with pairs that make builds, so that each function's result type is fixed by
((=) (Pair.iter ignore ignore (Pair.make Num Str)) Unit)
((=) (Pair.equal (=) (=) (Pair.make Num Str) (Pair.make Num Str)) true)
((=) (Pair.equal (=) (=) (Pair.make Num Str) (Pair.make Num Str)) Num)
((=) (Pair.compare compare compare (Pair.make Num Str) (Pair.make Num Str)) Num)
((=) (Pair.compare compare compare (Pair.make Num Str) (Pair.make Num Str)) true)
