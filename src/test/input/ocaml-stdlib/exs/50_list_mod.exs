// 0_basics.types, 1_comparison.types, 4_arith.types, 8_char.types, 50_list_mod.types

// length: 'a list -> int
(List.length Nil)
(List.length (List.cons Num Nil))
(List.length (List.cons Str (List.cons Str Nil)))
(List.length (List.cons true Nil))

// is_empty: 'a list -> bool
(List.is_empty Nil)
(List.is_empty (List.cons Num Nil))

// cons, singleton
(List.cons Num Nil)
(List.cons Str Nil)
(List.cons true Nil)
(List.singleton Num)
(List.singleton Str)
(List.singleton true)

// hd, tl
(List.hd (List.cons Num Nil))
(List.hd (List.cons Str Nil))
(List.hd (List.cons true Nil))
(List.tl (List.cons Num Nil))
(List.tl (List.cons Num (List.cons Num Nil)))

// nth, nth_opt
(List.nth (List.cons Num Nil) Num)
(List.nth (List.cons Str Nil) Num)
(List.nth_opt (List.cons Num Nil) Num)

// rev
(List.rev (List.cons Num Nil))
(List.rev (List.cons Str (List.cons Str Nil)))
(List.rev Nil)

// init: int -> (int -> 'a) -> 'a list
(List.init Num succ)
(List.init Num char_of_int)
(List.init Num (fun i1 -> i1))

// append, rev_append
(List.append (List.cons Num Nil) (List.cons Num Nil))
(List.append Nil (List.cons Str Nil))
(List.append (List.cons Str Nil) Nil)
(List.rev_append (List.cons Num Nil) (List.cons Num Nil))

// concat, flatten
(List.concat (List.cons (List.cons Num Nil) Nil))
(List.flatten (List.cons (List.cons Num Nil) Nil))

// map, mapi, rev_map
(List.map succ (List.cons Num Nil))
(List.map not (List.cons true Nil))
(List.map char_of_int (List.cons Num Nil))
(List.map abs (List.cons Num (List.cons Num Nil)))
(List.mapi (fun i2 x1 -> ((+) i2 x1)) (List.cons Num Nil))
(List.rev_map succ (List.cons Num Nil))

// filter, filter_map
(List.filter (fun x2 -> ((=) x2 Num)) (List.cons Num Nil))
(List.filter (fun x3 -> ((=) x3 Str)) (List.cons Str Nil))

// fold_left, fold_right
(List.fold_left (+) Num (List.cons Num Nil))
(List.fold_left (^) Str (List.cons Str Nil))
(List.fold_right (+) (List.cons Num Nil) Num)
(List.fold_right (^) (List.cons Str Nil) Str)

// for_all, exists
(List.for_all (fun x4 -> ((=) x4 Num)) (List.cons Num Nil))
(List.exists (fun x5 -> ((=) x5 Str)) (List.cons Str Nil))
(List.for_all (fun x6 -> ((=) x6 Num)) Nil)

// mem, memq
(List.mem Num (List.cons Num Nil))
(List.mem Str (List.cons Str Nil))
(List.mem true (List.cons true Nil))

// find, find_opt, find_index
(List.find (fun x7 -> ((=) x7 Num)) (List.cons Num Nil))
(List.find_opt (fun x8 -> ((=) x8 Num)) (List.cons Num Nil))
(List.find_index (fun x9 -> ((=) x9 Num)) (List.cons Num Nil))

// take, drop
(List.take Num (List.cons Num Nil))
(List.drop Num (List.cons Num Nil))
(List.take_while (fun x10 -> ((=) x10 Num)) (List.cons Num Nil))
(List.drop_while (fun x11 -> ((=) x11 Num)) (List.cons Num Nil))

// partition
(List.partition (fun x12 -> ((=) x12 Num)) (List.cons Num Nil))

// sort
(List.sort List.compare (List.cons Num Nil))
(List.stable_sort List.compare (List.cons Num Nil))
(List.sort List.compare (List.cons Str Nil))

// equal, compare
(List.equal (=) (List.cons Num Nil) (List.cons Num Nil))
(List.compare List.compare (List.cons Num Nil) (List.cons Num Nil))

// Chaining: length returns int
((=) (List.length (List.cons Num Nil)) Num)
((=) (List.length Nil) Num)
(succ (List.length (List.cons Num Nil)))
((=) (List.length (List.cons Num Nil)) Num)
(List.nth (List.cons Num Nil) (List.length Nil))
(List.take (List.length (List.cons Num Nil)) (List.cons Num Nil))
(List.drop (List.length (List.cons Num Nil)) (List.cons Num Nil))
(List.length (List.append (List.cons Num Nil) (List.cons Num Nil)))
(List.length (List.map succ (List.cons Num Nil)))
(List.length (List.filter (fun x13 -> ((=) x13 Num)) (List.cons Num Nil)))
(List.length (List.sort List.compare (List.cons Num Nil)))
((=) (List.length (List.map succ (List.cons Num Nil))) Num)

// hd returns element type
((=) (List.hd (List.cons Num Nil)) Num)
((=) (List.hd (List.cons Str Nil)) Str)
(succ (List.hd (List.cons Num Nil)))
((^) (List.hd (List.cons Str Nil)) Str)
(List.mem (List.hd (List.cons Num Nil)) (List.cons Num Nil))
(List.cons (List.hd (List.cons Num Nil)) (List.tl (List.cons Num Nil)))

// tl returns list — use in more list ops
(List.length (List.tl (List.cons Num (List.cons Num Nil))))
(List.hd (List.tl (List.cons Num (List.cons Num Nil))))
(List.rev (List.tl (List.cons Num (List.cons Num Nil))))
(List.append (List.tl (List.cons Num Nil)) (List.cons Num Nil))

// map returns list — chain into more list ops
(List.length (List.map succ (List.cons Num Nil)))
(List.hd (List.map succ (List.cons Num Nil)))
(List.rev (List.map succ (List.cons Num Nil)))
(List.map succ (List.map abs (List.cons Num Nil)))
(List.fold_left (+) Num (List.map succ (List.cons Num Nil)))
(List.for_all (fun x14 -> ((=) x14 Num)) (List.map succ (List.cons Num Nil)))
(List.mem (List.hd (List.map succ (List.cons Num Nil))) (List.map succ (List.cons Num Nil)))

// sort returns list — chain into more list ops
(List.hd (List.sort List.compare (List.cons Num Nil)))
(List.length (List.sort List.compare (List.cons Num Nil)))
(List.rev (List.sort List.compare (List.cons Num Nil)))
(List.equal (=) (List.sort List.compare (List.cons Num Nil)) (List.cons Num Nil))

// fold_left returns accumulator type
((=) (List.fold_left (+) Num (List.cons Num Nil)) Num)
(succ (List.fold_left (+) Num (List.cons Num Nil)))
(List.mem (List.fold_left (+) Num (List.cons Num Nil)) (List.cons Num Nil))
((=) (List.fold_left (^) Str (List.cons Str Nil)) Str)

// for_all / exists / is_empty / mem return bool
((=) (List.for_all (fun x15 -> ((=) x15 Num)) (List.cons Num Nil)) true)
((=) (List.is_empty Nil) true)
((=) (List.is_empty (List.cons Num Nil)) false)
(not (List.is_empty (List.cons Num Nil)))
(not (List.mem Num Nil))

// find returns element type
((=) (List.find (fun x16 -> ((=) x16 Num)) (List.cons Num Nil)) Num)
(succ (List.find (fun x17 -> ((=) x17 Num)) (List.cons Num Nil)))
(List.mem (List.find (fun x18 -> ((=) x18 Num)) (List.cons Num Nil)) (List.cons Num Nil))

// nth returns element type
((=) (List.nth (List.cons Num Nil) Num) Num)
(succ (List.nth (List.cons Num Nil) Num))
(List.nth (List.cons Num Nil) (List.nth (List.cons Num Nil) Num))

// rev returns list
(List.hd (List.rev (List.cons Num (List.cons Num Nil))))
((=) (List.hd (List.rev (List.cons Num Nil))) Num)
(List.length (List.rev (List.cons Num (List.cons Num Nil))))

// compare returns int
(succ (List.compare List.compare (List.cons Num Nil) (List.cons Num Nil)))
((=) (List.compare List.compare (List.cons Num Nil) (List.cons Num Nil)) Num)
((=) (List.compare List.compare (List.cons Num Nil) (List.cons Num Nil)) Num)

// equal returns bool
((=) (List.equal (=) (List.cons Num Nil) (List.cons Num Nil)) true)
(not (List.equal (=) (List.cons Num Nil) (List.cons Num Nil)))

// Invalid: outputs used at wrong type
(succ (List.hd (List.cons Str Nil)))
((^) (List.hd (List.cons Num Nil)) Str)
(not (List.hd (List.cons Num Nil)))
(not (List.length (List.cons Num Nil)))
((^) (List.length (List.cons Num Nil)) Str)
(List.mem Str (List.cons Num Nil))
(List.append (List.cons Num Nil) (List.cons Str Nil))
(List.equal (=) (List.cons Num Nil) (List.cons Str Nil))
(List.fold_left (+) Str (List.cons Num Nil))
(List.map succ (List.cons Str Nil))
(List.map not (List.cons Num Nil))
(succ (List.is_empty Nil))
(List.is_empty Num)
(List.length Num)
(List.hd Nil)
(succ (List.find_opt (fun x19 -> ((=) x19 Num)) (List.cons Num Nil)))
