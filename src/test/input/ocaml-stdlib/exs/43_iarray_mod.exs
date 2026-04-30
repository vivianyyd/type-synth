// 0_basics.types, 1_comparison.types, 4_arith.types, 9_unit.types, 10_strconv.types, 43_iarray_mod.types

// Construction
(init Num succ)
(init Num string_of_int)
(init Num (fun i1 -> i1))
(of_list (cons Num []))
(of_list (cons Str []))
(of_list (cons true []))
(of_array (Array.make Num Num))
(of_array (Array.make Num Str))

// Inspection
(length (init Num succ))
(length (of_list (cons Num [])))
(get (init Num succ) Num)
(get (of_list (cons Str [])) Num)

// Structural operations
(append (init Num succ) (init Num succ))
(append (of_list (cons Num [])) (of_list (cons Num [])))
(concat (cons (init Num succ) []))
(to_list (init Num succ))
(to_list (of_list (cons Num [])))
(to_array (init Num succ))

// sort: returns a NEW iarray (immutable!)
(sort compare (init Num succ))
(stable_sort compare (init Num succ))

// Higher-order: map
(map succ (init Num succ))
(map not (of_list (cons true [])))
(map string_of_int (init Num succ))

// Higher-order: iter
(iter ignore (init Num succ))
(iter print_int (init Num succ))

// Higher-order: fold_left
(fold_left (+) Num (init Num succ))
(fold_left (^) Str (of_list (cons Str [])))

// Higher-order: for_all, exists
(for_all (fun x1 -> (= x1 Num)) (init Num succ))
(exists (fun x2 -> (= x2 Str)) (of_list (cons Str [])))

// Higher-order: equal, compare
(equal (=) (init Num succ) (init Num succ))
(compare compare (init Num succ) (init Num succ))

// mem
(mem Num (init Num succ))
(mem Str (of_list (cons Str [])))

// Chaining: length returns int
(= (length (init Num succ)) Num)
(< (length (init Num succ)) Num)
(succ (length (init Num succ)))
(get (init Num succ) (length (init Num succ)))

// get returns element type
(= (get (init Num succ) Num) Num)
(succ (get (init Num succ) Num))
(+ (get (init Num succ) Num) Num)
(mem (get (init Num succ) Num) (init Num succ))

// map returns iarray: chain further ops
(length (map succ (init Num succ)))
(get (map succ (init Num succ)) Num)
(= (get (map succ (init Num succ)) Num) Num)
(for_all (fun x3 -> (= x3 Num)) (map succ (init Num succ)))

// sort returns iarray: further operations on result
(length (sort compare (init Num succ)))
(get (sort compare (init Num succ)) Num)
(equal (=) (sort compare (init Num succ)) (init Num succ))

// append returns iarray
(length (append (init Num succ) (init Num succ)))
(get (append (init Num succ) (init Num succ)) Num)

// fold_left returns accumulator type
(= (fold_left (+) Num (init Num succ)) Num)
(succ (fold_left (+) Num (init Num succ)))
(mem (fold_left (+) Num (init Num succ)) (init Num succ))

// compare returns int
(= (compare compare (init Num succ) (init Num succ)) Num)
(succ (compare compare (init Num succ) (init Num succ)))

// equal returns bool
(= (equal (=) (init Num succ) (init Num succ)) true)
(not (equal (=) (init Num succ) (init Num succ)))

// to_list output: use as a list
(= (to_list (init Num succ)) (cons Num []))
(length (to_list (init Num succ)))

// Invalid: wrong output types used in wrong contexts
(get (init Num succ) Str)
(append (init Num succ) (of_list (cons Str [])))
(mem Str (init Num succ))
(equal (=) (init Num succ) (of_list (cons Str [])))
(succ (length (init Num succ)) Num)
(not (length (init Num succ)))
(get (length (init Num succ)) Num)
(fold_left (+) Str (init Num succ))
