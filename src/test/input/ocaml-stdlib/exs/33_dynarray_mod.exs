// 0_basics.types, 1_comparison.types, 4_arith.types, 9_unit.types, 10_strconv.types, 14_stdout.types, 33_dynarray_mod.types

// Construction
(Dynarray.create Unit)
(Dynarray.make Num Num)
(Dynarray.make Num Str)
(Dynarray.make Num true)
(Dynarray.init Num succ)
(Dynarray.init Num string_of_int)

// Inspection
(Dynarray.length (Dynarray.create Unit))
(Dynarray.length (Dynarray.make Num Num))
(Dynarray.is_empty (Dynarray.create Unit))
(Dynarray.is_empty (Dynarray.make Num Num))
(Dynarray.get (Dynarray.make Num Num) Num)
(Dynarray.get (Dynarray.make Num Str) Num)
(Dynarray.get_last (Dynarray.make Num Num))
(Dynarray.get_last (Dynarray.make Num Str))
(Dynarray.find_last (Dynarray.make Num Num))
(Dynarray.find_last (Dynarray.make Num Str))
(Dynarray.capacity (Dynarray.make Num Num))

// Structural
(Dynarray.copy (Dynarray.make Num Num))
(Dynarray.copy (Dynarray.make Num Str))
(Dynarray.of_array (Array.make Num Num))
(Dynarray.of_list (cons Num []))
(Dynarray.of_list (cons Str []))
(Dynarray.to_array (Dynarray.make Num Num))
(Dynarray.to_list (Dynarray.make Num Num))
(Dynarray.to_list (Dynarray.make Num Str))

// Mutation
(Dynarray.add_last (Dynarray.make Num Num) Num)
(Dynarray.add_last (Dynarray.make Num Str) Str)
(Dynarray.append_list (Dynarray.make Num Num) (cons Num []))
(Dynarray.remove_last (Dynarray.make Num Num))
(Dynarray.pop_last (Dynarray.make Num Num))
(Dynarray.pop_last_opt (Dynarray.make Num Num))
(Dynarray.truncate (Dynarray.make Num Num) Num)
(Dynarray.clear (Dynarray.make Num Num))
(Dynarray.reset (Dynarray.make Num Num))
(Dynarray.ensure_capacity (Dynarray.make Num Num) Num)
(Dynarray.ensure_extra_capacity (Dynarray.make Num Num) Num)
(Dynarray.fit_capacity (Dynarray.make Num Num))

// Higher-order: iter
(Dynarray.iter ignore (Dynarray.make Num Num))
(Dynarray.iter print_int (Dynarray.make Num Num))
(Dynarray.iter print_string (Dynarray.make Num Str))

// Higher-order: map
(Dynarray.map succ (Dynarray.make Num Num))
(Dynarray.map not (Dynarray.make Num true))
(Dynarray.map string_of_int (Dynarray.make Num Num))

// Higher-order: filter
(Dynarray.filter (fun x1 -> ((=) x1 Num)) (Dynarray.make Num Num))
(Dynarray.filter (fun x2 -> ((=) x2 Str)) (Dynarray.make Num Str))

// Higher-order: fold_left
(Dynarray.fold_left (+) Num (Dynarray.make Num Num))
(Dynarray.fold_left (^) Str (Dynarray.make Num Str))

// Higher-order: for_all, exists
(Dynarray.for_all (fun x3 -> ((=) x3 Num)) (Dynarray.make Num Num))
(Dynarray.exists (fun x4 -> ((=) x4 Str)) (Dynarray.make Num Str))

// mem
(Dynarray.mem Num (Dynarray.make Num Num))
(Dynarray.mem Str (Dynarray.make Num Str))

// equal, compare
(Dynarray.equal (=) (Dynarray.make Num Num) (Dynarray.make Num Num))
(Dynarray.equal (=) (Dynarray.make Num Str) (Dynarray.make Num Str))
(Dynarray.compare Dynarray.compare (Dynarray.make Num Num) (Dynarray.make Num Num))

// Chaining: length returns int
((=) (Dynarray.length (Dynarray.make Num Num)) Num)
((<) (Dynarray.length (Dynarray.make Num Num)) Num)
(succ (Dynarray.length (Dynarray.make Num Num)))
(Dynarray.truncate (Dynarray.make Num Num) (Dynarray.length (Dynarray.make Num Num)))
(Dynarray.ensure_capacity (Dynarray.make Num Num) (Dynarray.length (Dynarray.make Num Num)))
(Dynarray.get (Dynarray.make Num Num) (Dynarray.length (Dynarray.make Num Num)))
(Dynarray.capacity (Dynarray.copy (Dynarray.make Num Num)))
((=) (Dynarray.capacity (Dynarray.make Num Num)) Num)

// is_empty returns bool
((=) (Dynarray.is_empty (Dynarray.create Unit)) true)
((=) (Dynarray.is_empty (Dynarray.make Num Num)) false)

// get returns element type
((=) (Dynarray.get (Dynarray.make Num Num) Num) Num)
((=) (Dynarray.get (Dynarray.make Num Str) Num) Str)
(succ (Dynarray.get (Dynarray.make Num Num) Num))
(Dynarray.add_last (Dynarray.make Num Num) (Dynarray.get (Dynarray.make Num Num) Num))
(Dynarray.mem (Dynarray.get (Dynarray.make Num Num) Num) (Dynarray.make Num Num))

// get_last returns element type
((=) (Dynarray.get_last (Dynarray.make Num Num)) Num)
(succ (Dynarray.get_last (Dynarray.make Num Num)))
(Dynarray.add_last (Dynarray.make Num Num) (Dynarray.get_last (Dynarray.make Num Num)))

// pop_last returns element type
((=) (Dynarray.pop_last (Dynarray.make Num Num)) Num)
(succ (Dynarray.pop_last (Dynarray.make Num Num)))

// map returns dynarray: inspect it
(Dynarray.length (Dynarray.map succ (Dynarray.make Num Num)))
(Dynarray.get (Dynarray.map succ (Dynarray.make Num Num)) Num)
(Dynarray.is_empty (Dynarray.map not (Dynarray.make Num true)))
(Dynarray.for_all (fun x5 -> ((=) x5 Num)) (Dynarray.map succ (Dynarray.make Num Num)))

// fold_left returns accumulator type
((=) (Dynarray.fold_left (+) Num (Dynarray.make Num Num)) Num)
(succ (Dynarray.fold_left (+) Num (Dynarray.make Num Num)))

// to_list returns list
((=) (Dynarray.to_list (Dynarray.make Num Num)) (cons Num []))

// of_list / to_list roundtrip
(Dynarray.equal (=) (Dynarray.of_list (Dynarray.to_list (Dynarray.make Num Num))) (Dynarray.make Num Num))

// Invalid
(Dynarray.get (Dynarray.make Num Num) Str)
(Dynarray.add_last (Dynarray.make Num Num) Str)
(Dynarray.mem Str (Dynarray.make Num Num))
(Dynarray.equal (=) (Dynarray.make Num Num) (Dynarray.make Num Str))
(Dynarray.fold_left (+) Str (Dynarray.make Num Num))
