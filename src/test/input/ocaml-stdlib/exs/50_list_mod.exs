// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 9_unit.types, 10_strconv.types, 14_stdout.types, 50_list_mod.exs

// length: 'a list -> int
(List.length [])
(List.length (List.cons Num []))
(List.length (List.cons Str (List.cons Str [])))
(List.length (List.cons true []))

// is_empty: 'a list -> bool
(List.is_empty [])
(List.is_empty (List.cons Num []))

// cons, singleton
(List.cons Num [])
(List.cons Str [])
(List.cons true [])
(List.singleton Num)
(List.singleton Str)
(List.singleton true)

// hd, tl
(List.hd (List.cons Num []))
(List.hd (List.cons Str []))
(List.hd (List.cons true []))
(List.tl (List.cons Num []))
(List.tl (List.cons Num (List.cons Num [])))

// nth, nth_opt
(List.nth (List.cons Num []) Num)
(List.nth (List.cons Str []) Num)
(List.nth_opt (List.cons Num []) Num)

// rev
(List.rev (List.cons Num []))
(List.rev (List.cons Str (List.cons Str [])))
(List.rev [])

// init: int -> (int -> 'a) -> 'a list
(List.init Num succ)
(List.init Num string_of_int)
(List.init Num (fun i1 -> i1))

// append, rev_append
(List.append (List.cons Num []) (List.cons Num []))
(List.append [] (List.cons Str []))
(List.append (List.cons Str []) [])
(List.rev_append (List.cons Num []) (List.cons Num []))

// concat, flatten
(List.concat (List.cons (List.cons Num []) []))
(List.flatten (List.cons (List.cons Num []) []))

// map, mapi, rev_map
(List.map succ (List.cons Num []))
(List.map not (List.cons true []))
(List.map string_of_int (List.cons Num []))
(List.map abs (List.cons Num (List.cons Num [])))
(List.mapi (fun i2 x1 -> ((+) i2 x1)) (List.cons Num []))
(List.rev_map succ (List.cons Num []))

// filter, filter_map
(List.filter (fun x2 -> ((=) x2 Num)) (List.cons Num []))
(List.filter (fun x3 -> ((=) x3 Str)) (List.cons Str []))

// fold_left, fold_right
(List.fold_left (+) Num (List.cons Num []))
(List.fold_left (^) Str (List.cons Str []))
(List.fold_left max Num (List.cons Num []))
(List.fold_right (+) (List.cons Num []) Num)
(List.fold_right (^) (List.cons Str []) Str)

// for_all, exists
(List.for_all (fun x4 -> ((=) x4 Num)) (List.cons Num []))
(List.exists (fun x5 -> ((=) x5 Str)) (List.cons Str []))
(List.for_all (fun x6 -> ((=) x6 Num)) [])

// mem, memq
(List.mem Num (List.cons Num []))
(List.mem Str (List.cons Str []))
(List.mem true (List.cons true []))

// find, find_opt, find_index
(List.find (fun x7 -> ((=) x7 Num)) (List.cons Num []))
(List.find_opt (fun x8 -> ((=) x8 Num)) (List.cons Num []))
(List.find_index (fun x9 -> ((=) x9 Num)) (List.cons Num []))

// take, drop
(List.take Num (List.cons Num []))
(List.drop Num (List.cons Num []))
(List.take_while (fun x10 -> ((=) x10 Num)) (List.cons Num []))
(List.drop_while (fun x11 -> ((=) x11 Num)) (List.cons Num []))

// partition
(List.partition (fun x12 -> ((=) x12 Num)) (List.cons Num []))

// sort
(List.sort List.compare (List.cons Num []))
(List.stable_sort List.compare (List.cons Num []))
(List.sort List.compare (List.cons Str []))

// equal, compare
(List.equal (=) (List.cons Num []) (List.cons Num []))
(List.compare List.compare (List.cons Num []) (List.cons Num []))

// Chaining: length returns int
((=) (List.length (List.cons Num [])) Num)
((=) (List.length []) Num)
(succ (List.length (List.cons Num [])))
((<) (List.length (List.cons Num [])) Num)
(List.nth (List.cons Num []) (List.length []))
(List.take (List.length (List.cons Num [])) (List.cons Num []))
(List.drop (List.length (List.cons Num [])) (List.cons Num []))
(List.length (List.append (List.cons Num []) (List.cons Num [])))
(List.length (List.map succ (List.cons Num [])))
(List.length (List.filter (fun x13 -> ((=) x13 Num)) (List.cons Num [])))
(List.length (List.sort List.compare (List.cons Num [])))
((=) (List.length (List.map succ (List.cons Num []))) Num)

// hd returns element type
((=) (List.hd (List.cons Num [])) Num)
((=) (List.hd (List.cons Str [])) Str)
(succ (List.hd (List.cons Num [])))
((^) (List.hd (List.cons Str [])) Str)
(List.mem (List.hd (List.cons Num [])) (List.cons Num []))
(List.cons (List.hd (List.cons Num [])) (List.tl (List.cons Num [])))

// tl returns list — use in more list ops
(List.length (List.tl (List.cons Num (List.cons Num []))))
(List.hd (List.tl (List.cons Num (List.cons Num []))))
(List.rev (List.tl (List.cons Num (List.cons Num []))))
(List.append (List.tl (List.cons Num [])) (List.cons Num []))

// map returns list — chain into more list ops
(List.length (List.map succ (List.cons Num [])))
(List.hd (List.map succ (List.cons Num [])))
(List.rev (List.map succ (List.cons Num [])))
(List.map succ (List.map abs (List.cons Num [])))
(List.fold_left (+) Num (List.map succ (List.cons Num [])))
(List.for_all (fun x14 -> ((=) x14 Num)) (List.map succ (List.cons Num [])))
(List.mem (List.hd (List.map succ (List.cons Num []))) (List.map succ (List.cons Num [])))

// sort returns list — chain into more list ops
(List.hd (List.sort List.compare (List.cons Num [])))
(List.length (List.sort List.compare (List.cons Num [])))
(List.rev (List.sort List.compare (List.cons Num [])))
(List.equal (=) (List.sort List.compare (List.cons Num [])) (List.cons Num []))

// fold_left returns accumulator type
((=) (List.fold_left (+) Num (List.cons Num [])) Num)
(succ (List.fold_left (+) Num (List.cons Num [])))
(List.mem (List.fold_left (+) Num (List.cons Num [])) (List.cons Num []))
((=) (List.fold_left (^) Str (List.cons Str [])) Str)

// for_all / exists / is_empty / mem return bool
((=) (List.for_all (fun x15 -> ((=) x15 Num)) (List.cons Num [])) true)
((=) (List.is_empty []) true)
((=) (List.is_empty (List.cons Num [])) false)
(not (List.is_empty (List.cons Num [])))
(not (List.mem Num []))

// find returns element type
((=) (List.find (fun x16 -> ((=) x16 Num)) (List.cons Num [])) Num)
(succ (List.find (fun x17 -> ((=) x17 Num)) (List.cons Num [])))
(List.mem (List.find (fun x18 -> ((=) x18 Num)) (List.cons Num [])) (List.cons Num []))

// nth returns element type
((=) (List.nth (List.cons Num []) Num) Num)
(succ (List.nth (List.cons Num []) Num))
(List.nth (List.cons Num []) (List.nth (List.cons Num []) Num))

// rev returns list
(List.hd (List.rev (List.cons Num (List.cons Num []))))
((=) (List.hd (List.rev (List.cons Num []))) Num)
(List.length (List.rev (List.cons Num (List.cons Num []))))

// compare returns int
(succ (List.compare List.compare (List.cons Num []) (List.cons Num [])))
((=) (List.compare List.compare (List.cons Num []) (List.cons Num [])) Num)
((<) (List.compare List.compare (List.cons Num []) (List.cons Num [])) Num)

// equal returns bool
((=) (List.equal (=) (List.cons Num []) (List.cons Num [])) true)
(not (List.equal (=) (List.cons Num []) (List.cons Num [])))

// Invalid: outputs used at wrong type
(succ (List.hd (List.cons Str [])))
((^) (List.hd (List.cons Num [])) Str)
(not (List.hd (List.cons Num [])))
(not (List.length (List.cons Num [])))
((^) (List.length (List.cons Num [])) Str)
(List.mem Str (List.cons Num []))
(List.append (List.cons Num []) (List.cons Str []))
(List.equal (=) (List.cons Num []) (List.cons Str []))
(List.fold_left (+) Str (List.cons Num []))
(List.map succ (List.cons Str []))
(List.map not (List.cons Num []))
(succ (List.is_empty []))
(List.is_empty Num)
(List.length Num)
(List.hd [])
(succ (List.find_opt (fun x19 -> ((=) x19 Num)) (List.cons Num [])))
