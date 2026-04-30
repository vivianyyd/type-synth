// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 76_pair_mod.types

// make: 'a -> 'b -> 'a * 'b
(Pair.make Num Str)
(Pair.make Str Num)
(Pair.make Num Num)
(Pair.make true Str)
(Pair.make Num true)

// fst: 'a * 'b -> 'a
(Pair.fst (Pair.make Num Str))
(Pair.fst (Pair.make Str Num))
(Pair.fst (Pair.make true Num))

// snd: 'a * 'b -> 'b
(Pair.snd (Pair.make Num Str))
(Pair.snd (Pair.make Str Num))
(Pair.snd (Pair.make Num true))

// swap: 'a * 'b -> 'b * 'a
(Pair.swap (Pair.make Num Str))
(Pair.swap (Pair.make Str Num))
(Pair.swap (Pair.make true Num))

// fold: ('a -> 'b -> 'c) -> 'a * 'b -> 'c
(Pair.fold (+) (Pair.make Num Num))
(Pair.fold (^) (Pair.make Str Str))
(Pair.fold (=) (Pair.make Num Num))

// map: ('a -> 'c) -> ('b -> 'd) -> 'a * 'b -> 'c * 'd
(Pair.map succ not (Pair.make Num true))
(Pair.map string_of_int string_of_bool (Pair.make Num true))
(Pair.map not succ (Pair.make true Num))

// iter: ('a -> unit) -> ('b -> unit) -> 'a * 'b -> unit
(Pair.iter print_int print_string (Pair.make Num Str))
(Pair.iter ignore ignore (Pair.make Num Str))

// map_fst: ('a -> 'c) -> 'a * 'b -> 'c * 'b
(Pair.map_fst succ (Pair.make Num Str))
(Pair.map_fst not (Pair.make true Num))
(Pair.map_fst string_of_int (Pair.make Num Str))

// map_snd: ('b -> 'c) -> 'a * 'b -> 'a * 'c
(Pair.map_snd succ (Pair.make Str Num))
(Pair.map_snd not (Pair.make Num true))
(Pair.map_snd string_of_int (Pair.make Str Num))

// equal: ('a -> 'a -> bool) -> ('b -> 'b -> bool) -> 'a * 'b -> 'a * 'b -> bool
(Pair.equal (=) (=) (Pair.make Num Str) (Pair.make Num Str))
(Pair.equal (=) (=) (Pair.make Str Num) (Pair.make Str Num))

// compare: ('a -> 'a -> int) -> ('b -> 'b -> int) -> 'a * 'b -> 'a * 'b -> int
(Pair.compare Pair.compare Pair.compare (Pair.make Num Str) (Pair.make Num Str))

// Chaining: fst/snd extract components — use in type-appropriate ops
((=) (Pair.fst (Pair.make Num Str)) Num)
(succ (Pair.fst (Pair.make Num Str)))
((^) (Pair.snd (Pair.make Num Str)) Str)
(not (Pair.snd (Pair.make Num true)))
((=) (Pair.fst (Pair.make Str Num)) Str)
((+) (Pair.fst (Pair.make Num Num)) (Pair.snd (Pair.make Num Num)))
((=) (Pair.fst (Pair.make Num Str)) (Pair.fst (Pair.make Num Str)))
((=) (Pair.snd (Pair.make Num Str)) (Pair.snd (Pair.make Num Str)))

// swap returns swapped pair — fst/snd now flipped
(Pair.fst (Pair.swap (Pair.make Num Str)))
(Pair.snd (Pair.swap (Pair.make Num Str)))
((=) (Pair.fst (Pair.swap (Pair.make Num Str))) Str)
((=) (Pair.snd (Pair.swap (Pair.make Num Str))) Num)
(succ (Pair.snd (Pair.swap (Pair.make Num Str))))
(Pair.swap (Pair.swap (Pair.make Num Str)))
((=) (Pair.fst (Pair.swap (Pair.swap (Pair.make Num Str)))) Num)

// fold returns result of combining both components
((=) (Pair.fold (+) (Pair.make Num Num)) Num)
(succ (Pair.fold (+) (Pair.make Num Num)))
((=) (Pair.fold (^) (Pair.make Str Str)) Str)
((^) (Pair.fold (^) (Pair.make Str Str)) Str)
(not (Pair.fold (=) (Pair.make Num Num)))

// map returns new pair — fst/snd give new types
(Pair.fst (Pair.map succ not (Pair.make Num true)))
(Pair.snd (Pair.map succ not (Pair.make Num true)))
((=) (Pair.fst (Pair.map succ not (Pair.make Num true))) Num)
(not (Pair.snd (Pair.map succ not (Pair.make Num true))))
(Pair.fst (Pair.map_fst succ (Pair.make Num Str)))
(Pair.snd (Pair.map_snd succ (Pair.make Str Num)))
((=) (Pair.fst (Pair.map_fst succ (Pair.make Num Str))) Num)
(succ (Pair.fst (Pair.map_fst succ (Pair.make Num Str))))
((=) (Pair.snd (Pair.map_snd succ (Pair.make Str Num))) Num)

// equal returns bool
((=) (Pair.equal (=) (=) (Pair.make Num Str) (Pair.make Num Str)) true)
(not (Pair.equal (=) (=) (Pair.make Num Str) (Pair.make Num Str)))
((&&) (Pair.equal (=) (=) (Pair.make Num Str) (Pair.make Num Str)) (Pair.equal (=) (=) (Pair.make Str Num) (Pair.make Str Num)))

// compare returns int
((=) (Pair.compare Pair.compare Pair.compare (Pair.make Num Str) (Pair.make Num Str)) Num)
(succ (Pair.compare Pair.compare Pair.compare (Pair.make Num Str) (Pair.make Num Str)))

// Invalid
(succ (Pair.make Num Str))
(not (Pair.make true Num))
(Pair.fst (Pair.fst (Pair.make Num Str)))
((=) (Pair.fst (Pair.make Num Str)) (Pair.snd (Pair.make Num Str)))
((=) (Pair.fst (Pair.make Num Str)) Str)
(Pair.fold (+) (Pair.make Num Str))
(Pair.map succ succ (Pair.make Num true))
(Pair.equal (=) (=) (Pair.make Num Str) (Pair.make Str Num))
