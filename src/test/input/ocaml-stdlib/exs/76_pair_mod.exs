// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 76_pair_mod.types

// make: 'a -> 'b -> 'a * 'b
(make Num Str)
(make Str Num)
(make Num Num)
(make true Str)
(make Num true)

// fst: 'a * 'b -> 'a
(fst (make Num Str))
(fst (make Str Num))
(fst (make true Num))

// snd: 'a * 'b -> 'b
(snd (make Num Str))
(snd (make Str Num))
(snd (make Num true))

// swap: 'a * 'b -> 'b * 'a
(swap (make Num Str))
(swap (make Str Num))
(swap (make true Num))

// fold: ('a -> 'b -> 'c) -> 'a * 'b -> 'c
(fold (+) (make Num Num))
(fold (^) (make Str Str))
(fold (=) (make Num Num))

// map: ('a -> 'c) -> ('b -> 'd) -> 'a * 'b -> 'c * 'd
(map succ not (make Num true))
(map string_of_int string_of_bool (make Num true))
(map not succ (make true Num))

// iter: ('a -> unit) -> ('b -> unit) -> 'a * 'b -> unit
(iter print_int print_string (make Num Str))
(iter ignore ignore (make Num Str))

// map_fst: ('a -> 'c) -> 'a * 'b -> 'c * 'b
(map_fst succ (make Num Str))
(map_fst not (make true Num))
(map_fst string_of_int (make Num Str))

// map_snd: ('b -> 'c) -> 'a * 'b -> 'a * 'c
(map_snd succ (make Str Num))
(map_snd not (make Num true))
(map_snd string_of_int (make Str Num))

// equal: ('a -> 'a -> bool) -> ('b -> 'b -> bool) -> 'a * 'b -> 'a * 'b -> bool
(equal (=) (=) (make Num Str) (make Num Str))
(equal (=) (=) (make Str Num) (make Str Num))

// compare: ('a -> 'a -> int) -> ('b -> 'b -> int) -> 'a * 'b -> 'a * 'b -> int
(compare compare compare (make Num Str) (make Num Str))

// Chaining: fst/snd extract components — use in type-appropriate ops
(= (fst (make Num Str)) Num)
(succ (fst (make Num Str)))
(^ (snd (make Num Str)) Str)
(not (snd (make Num true)))
(= (fst (make Str Num)) Str)
(+ (fst (make Num Num)) (snd (make Num Num)))
(= (fst (make Num Str)) (fst (make Num Str)))
(= (snd (make Num Str)) (snd (make Num Str)))

// swap returns swapped pair — fst/snd now flipped
(fst (swap (make Num Str)))
(snd (swap (make Num Str)))
(= (fst (swap (make Num Str))) Str)
(= (snd (swap (make Num Str))) Num)
(succ (snd (swap (make Num Str))))
(swap (swap (make Num Str)))
(= (fst (swap (swap (make Num Str)))) Num)

// fold returns result of combining both components
(= (fold (+) (make Num Num)) Num)
(succ (fold (+) (make Num Num)))
(= (fold (^) (make Str Str)) Str)
(^ (fold (^) (make Str Str)) Str)
(not (fold (=) (make Num Num)))

// map returns new pair — fst/snd give new types
(fst (map succ not (make Num true)))
(snd (map succ not (make Num true)))
(= (fst (map succ not (make Num true))) Num)
(not (snd (map succ not (make Num true))))
(fst (map_fst succ (make Num Str)))
(snd (map_snd succ (make Str Num)))
(= (fst (map_fst succ (make Num Str))) Num)
(succ (fst (map_fst succ (make Num Str))))
(= (snd (map_snd succ (make Str Num))) Num)

// equal returns bool
(= (equal (=) (=) (make Num Str) (make Num Str)) true)
(not (equal (=) (=) (make Num Str) (make Num Str)))
(&& (equal (=) (=) (make Num Str) (make Num Str)) (equal (=) (=) (make Str Num) (make Str Num)))

// compare returns int
(= (compare compare compare (make Num Str) (make Num Str)) Num)
(succ (compare compare compare (make Num Str) (make Num Str)))

// Invalid
(succ (make Num Str))
(not (make true Num))
(fst (fst (make Num Str)))
(= (fst (make Num Str)) (snd (make Num Str)))
(= (fst (make Num Str)) Str)
(fold (+) (make Num Str))
(map succ succ (make Num true))
(equal (=) (=) (make Num Str) (make Str Num))
