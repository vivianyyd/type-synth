// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 9_unit.types, 10_strconv.types, 14_stdout.types, 50_list_mod.exs

// length: 'a list -> int
(length [])
(length (cons Num []))
(length (cons Str (cons Str [])))
(length (cons true []))

// is_empty: 'a list -> bool
(is_empty [])
(is_empty (cons Num []))

// cons, singleton
(cons Num [])
(cons Str [])
(cons true [])
(singleton Num)
(singleton Str)
(singleton true)

// hd, tl
(hd (cons Num []))
(hd (cons Str []))
(hd (cons true []))
(tl (cons Num []))
(tl (cons Num (cons Num [])))

// nth, nth_opt
(nth (cons Num []) Num)
(nth (cons Str []) Num)
(nth_opt (cons Num []) Num)

// rev
(rev (cons Num []))
(rev (cons Str (cons Str [])))
(rev [])

// init: int -> (int -> 'a) -> 'a list
(init Num succ)
(init Num string_of_int)
(init Num (fun i1 -> i1))

// append, rev_append
(append (cons Num []) (cons Num []))
(append [] (cons Str []))
(append (cons Str []) [])
(rev_append (cons Num []) (cons Num []))

// concat, flatten
(concat (cons (cons Num []) []))
(flatten (cons (cons Num []) []))

// map, mapi, rev_map
(map succ (cons Num []))
(map not (cons true []))
(map string_of_int (cons Num []))
(map abs (cons Num (cons Num [])))
(mapi (fun i2 x1 -> (+ i2 x1)) (cons Num []))
(rev_map succ (cons Num []))

// filter, filter_map
(filter (fun x2 -> (= x2 Num)) (cons Num []))
(filter (fun x3 -> (= x3 Str)) (cons Str []))

// fold_left, fold_right
(fold_left (+) Num (cons Num []))
(fold_left (^) Str (cons Str []))
(fold_left max Num (cons Num []))
(fold_right (+) (cons Num []) Num)
(fold_right (^) (cons Str []) Str)

// for_all, exists
(for_all (fun x4 -> (= x4 Num)) (cons Num []))
(exists (fun x5 -> (= x5 Str)) (cons Str []))
(for_all (fun x6 -> (= x6 Num)) [])

// mem, memq
(mem Num (cons Num []))
(mem Str (cons Str []))
(mem true (cons true []))

// find, find_opt, find_index
(find (fun x7 -> (= x7 Num)) (cons Num []))
(find_opt (fun x8 -> (= x8 Num)) (cons Num []))
(find_index (fun x9 -> (= x9 Num)) (cons Num []))

// take, drop
(take Num (cons Num []))
(drop Num (cons Num []))
(take_while (fun x10 -> (= x10 Num)) (cons Num []))
(drop_while (fun x11 -> (= x11 Num)) (cons Num []))

// partition
(partition (fun x12 -> (= x12 Num)) (cons Num []))

// sort
(sort compare (cons Num []))
(stable_sort compare (cons Num []))
(sort compare (cons Str []))

// equal, compare
(equal (=) (cons Num []) (cons Num []))
(compare compare (cons Num []) (cons Num []))

// Chaining: length returns int
(= (length (cons Num [])) Num)
(= (length []) Num)
(succ (length (cons Num [])))
(< (length (cons Num [])) Num)
(nth (cons Num []) (length []))
(take (length (cons Num [])) (cons Num []))
(drop (length (cons Num [])) (cons Num []))
(length (append (cons Num []) (cons Num [])))
(length (map succ (cons Num [])))
(length (filter (fun x13 -> (= x13 Num)) (cons Num [])))
(length (sort compare (cons Num [])))
(= (length (map succ (cons Num []))) Num)

// hd returns element type
(= (hd (cons Num [])) Num)
(= (hd (cons Str [])) Str)
(succ (hd (cons Num [])))
(^ (hd (cons Str [])) Str)
(mem (hd (cons Num [])) (cons Num []))
(cons (hd (cons Num [])) (tl (cons Num [])))

// tl returns list — use in more list ops
(length (tl (cons Num (cons Num []))))
(hd (tl (cons Num (cons Num []))))
(rev (tl (cons Num (cons Num []))))
(append (tl (cons Num [])) (cons Num []))

// map returns list — chain into more list ops
(length (map succ (cons Num [])))
(hd (map succ (cons Num [])))
(rev (map succ (cons Num [])))
(map succ (map abs (cons Num [])))
(fold_left (+) Num (map succ (cons Num [])))
(for_all (fun x14 -> (= x14 Num)) (map succ (cons Num [])))
(mem (hd (map succ (cons Num []))) (map succ (cons Num [])))

// sort returns list — chain into more list ops
(hd (sort compare (cons Num [])))
(length (sort compare (cons Num [])))
(rev (sort compare (cons Num [])))
(equal (=) (sort compare (cons Num [])) (cons Num []))

// fold_left returns accumulator type
(= (fold_left (+) Num (cons Num [])) Num)
(succ (fold_left (+) Num (cons Num [])))
(mem (fold_left (+) Num (cons Num [])) (cons Num []))
(= (fold_left (^) Str (cons Str [])) Str)

// for_all / exists / is_empty / mem return bool
(= (for_all (fun x15 -> (= x15 Num)) (cons Num [])) true)
(= (is_empty []) true)
(= (is_empty (cons Num [])) false)
(not (is_empty (cons Num [])))
(not (mem Num []))

// find returns element type
(= (find (fun x16 -> (= x16 Num)) (cons Num [])) Num)
(succ (find (fun x17 -> (= x17 Num)) (cons Num [])))
(mem (find (fun x18 -> (= x18 Num)) (cons Num [])) (cons Num []))

// nth returns element type
(= (nth (cons Num []) Num) Num)
(succ (nth (cons Num []) Num))
(nth (cons Num []) (nth (cons Num []) Num))

// rev returns list
(hd (rev (cons Num (cons Num []))))
(= (hd (rev (cons Num []))) Num)
(length (rev (cons Num (cons Num []))))

// compare returns int
(succ (compare compare (cons Num []) (cons Num [])))
(= (compare compare (cons Num []) (cons Num [])) Num)
(< (compare compare (cons Num []) (cons Num [])) Num)

// equal returns bool
(= (equal (=) (cons Num []) (cons Num [])) true)
(not (equal (=) (cons Num []) (cons Num [])))

// Invalid: outputs used at wrong type
(succ (hd (cons Str [])))
(^ (hd (cons Num [])) Str)
(not (hd (cons Num [])))
(not (length (cons Num [])))
(^ (length (cons Num [])) Str)
(mem Str (cons Num []))
(append (cons Num []) (cons Str []))
(equal (=) (cons Num []) (cons Str []))
(fold_left (+) Str (cons Num []))
(map succ (cons Str []))
(map not (cons Num []))
(succ (is_empty []))
(is_empty Num)
(length Num)
(hd [])
(succ (find_opt (fun x19 -> (= x19 Num)) (cons Num [])))
