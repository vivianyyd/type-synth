// 0_basics.types, 1_comparison.types, 4_arith.types, 9_unit.types, 10_strconv.types, 14_stdout.types, 33_dynarray_mod.types

// Construction
(create Unit)
(make Num Num)
(make Num Str)
(make Num true)
(init Num succ)
(init Num string_of_int)

// Inspection
(length (create Unit))
(length (make Num Num))
(is_empty (create Unit))
(is_empty (make Num Num))
(get (make Num Num) Num)
(get (make Num Str) Num)
(get_last (make Num Num))
(get_last (make Num Str))
(find_last (make Num Num))
(find_last (make Num Str))
(capacity (make Num Num))

// Structural
(copy (make Num Num))
(copy (make Num Str))
(of_array (Array.make Num Num))
(of_list (cons Num []))
(of_list (cons Str []))
(to_array (make Num Num))
(to_list (make Num Num))
(to_list (make Num Str))

// Mutation
(add_last (make Num Num) Num)
(add_last (make Num Str) Str)
(append_list (make Num Num) (cons Num []))
(remove_last (make Num Num))
(pop_last (make Num Num))
(pop_last_opt (make Num Num))
(truncate (make Num Num) Num)
(clear (make Num Num))
(reset (make Num Num))
(ensure_capacity (make Num Num) Num)
(ensure_extra_capacity (make Num Num) Num)
(fit_capacity (make Num Num))

// Higher-order: iter
(iter ignore (make Num Num))
(iter print_int (make Num Num))
(iter print_string (make Num Str))

// Higher-order: map
(map succ (make Num Num))
(map not (make Num true))
(map string_of_int (make Num Num))

// Higher-order: filter
(filter (fun x1 -> (= x1 Num)) (make Num Num))
(filter (fun x2 -> (= x2 Str)) (make Num Str))

// Higher-order: fold_left
(fold_left (+) Num (make Num Num))
(fold_left (^) Str (make Num Str))

// Higher-order: for_all, exists
(for_all (fun x3 -> (= x3 Num)) (make Num Num))
(exists (fun x4 -> (= x4 Str)) (make Num Str))

// mem
(mem Num (make Num Num))
(mem Str (make Num Str))

// equal, compare
(equal (=) (make Num Num) (make Num Num))
(equal (=) (make Num Str) (make Num Str))
(compare compare (make Num Num) (make Num Num))

// Chaining: length returns int
(= (length (make Num Num)) Num)
(< (length (make Num Num)) Num)
(succ (length (make Num Num)))
(truncate (make Num Num) (length (make Num Num)))
(ensure_capacity (make Num Num) (length (make Num Num)))
(get (make Num Num) (length (make Num Num)))
(capacity (copy (make Num Num)))
(= (capacity (make Num Num)) Num)

// is_empty returns bool
(= (is_empty (create Unit)) true)
(= (is_empty (make Num Num)) false)

// get returns element type
(= (get (make Num Num) Num) Num)
(= (get (make Num Str) Num) Str)
(succ (get (make Num Num) Num))
(add_last (make Num Num) (get (make Num Num) Num))
(mem (get (make Num Num) Num) (make Num Num))

// get_last returns element type
(= (get_last (make Num Num)) Num)
(succ (get_last (make Num Num)))
(add_last (make Num Num) (get_last (make Num Num)))

// pop_last returns element type
(= (pop_last (make Num Num)) Num)
(succ (pop_last (make Num Num)))

// map returns dynarray: inspect it
(length (map succ (make Num Num)))
(get (map succ (make Num Num)) Num)
(is_empty (map not (make Num true)))
(for_all (fun x5 -> (= x5 Num)) (map succ (make Num Num)))

// fold_left returns accumulator type
(= (fold_left (+) Num (make Num Num)) Num)
(succ (fold_left (+) Num (make Num Num)))

// to_list returns list
(= (to_list (make Num Num)) (cons Num []))

// of_list / to_list roundtrip
(equal (=) (of_list (to_list (make Num Num))) (make Num Num))

// Invalid
(get (make Num Num) Str)
(add_last (make Num Num) Str)
(mem Str (make Num Num))
(equal (=) (make Num Num) (make Num Str))
(fold_left (+) Str (make Num Num))
