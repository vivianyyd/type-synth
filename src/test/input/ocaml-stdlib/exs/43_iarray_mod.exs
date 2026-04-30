// 0_basics.types, 1_comparison.types, 4_arith.types, 9_unit.types, 10_strconv.types, 43_iarray_mod.types

// Construction
(Iarray.init Num succ)
(Iarray.init Num string_of_int)
(Iarray.init Num (fun i1 -> i1))
(Iarray.of_list (cons Num []))
(Iarray.of_list (cons Str []))
(Iarray.of_list (cons true []))
(Iarray.of_array (Array.make Num Num))
(Iarray.of_array (Array.make Num Str))

// Inspection
(Iarray.length (Iarray.init Num succ))
(Iarray.length (Iarray.of_list (cons Num [])))
(Iarray.get (Iarray.init Num succ) Num)
(Iarray.get (Iarray.of_list (cons Str [])) Num)

// Structural operations
(Iarray.append (Iarray.init Num succ) (Iarray.init Num succ))
(Iarray.append (Iarray.of_list (cons Num [])) (Iarray.of_list (cons Num [])))
(Iarray.concat (cons (Iarray.init Num succ) []))
(Iarray.to_list (Iarray.init Num succ))
(Iarray.to_list (Iarray.of_list (cons Num [])))
(Iarray.to_array (Iarray.init Num succ))

// sort: returns a NEW iarray (immutable!)
(Iarray.sort Iarray.compare (Iarray.init Num succ))
(Iarray.stable_sort Iarray.compare (Iarray.init Num succ))

// Higher-order: map
(Iarray.map succ (Iarray.init Num succ))
(Iarray.map not (Iarray.of_list (cons true [])))
(Iarray.map string_of_int (Iarray.init Num succ))

// Higher-order: iter
(Iarray.iter ignore (Iarray.init Num succ))
(Iarray.iter print_int (Iarray.init Num succ))

// Higher-order: fold_left
(Iarray.fold_left (+) Num (Iarray.init Num succ))
(Iarray.fold_left (^) Str (Iarray.of_list (cons Str [])))

// Higher-order: for_all, exists
(Iarray.for_all (fun x1 -> ((=) x1 Num)) (Iarray.init Num succ))
(Iarray.exists (fun x2 -> ((=) x2 Str)) (Iarray.of_list (cons Str [])))

// Higher-order: equal, compare
(Iarray.equal (=) (Iarray.init Num succ) (Iarray.init Num succ))
(Iarray.compare Iarray.compare (Iarray.init Num succ) (Iarray.init Num succ))

// mem
(Iarray.mem Num (Iarray.init Num succ))
(Iarray.mem Str (Iarray.of_list (cons Str [])))

// Chaining: length returns int
((=) (Iarray.length (Iarray.init Num succ)) Num)
((<) (Iarray.length (Iarray.init Num succ)) Num)
(succ (Iarray.length (Iarray.init Num succ)))
(Iarray.get (Iarray.init Num succ) (Iarray.length (Iarray.init Num succ)))

// get returns element type
((=) (Iarray.get (Iarray.init Num succ) Num) Num)
(succ (Iarray.get (Iarray.init Num succ) Num))
((+) (Iarray.get (Iarray.init Num succ) Num) Num)
(Iarray.mem (Iarray.get (Iarray.init Num succ) Num) (Iarray.init Num succ))

// map returns iarray: chain further ops
(Iarray.length (Iarray.map succ (Iarray.init Num succ)))
(Iarray.get (Iarray.map succ (Iarray.init Num succ)) Num)
((=) (Iarray.get (Iarray.map succ (Iarray.init Num succ)) Num) Num)
(Iarray.for_all (fun x3 -> ((=) x3 Num)) (Iarray.map succ (Iarray.init Num succ)))

// sort returns iarray: further operations on result
(Iarray.length (Iarray.sort Iarray.compare (Iarray.init Num succ)))
(Iarray.get (Iarray.sort Iarray.compare (Iarray.init Num succ)) Num)
(Iarray.equal (=) (Iarray.sort Iarray.compare (Iarray.init Num succ)) (Iarray.init Num succ))

// append returns iarray
(Iarray.length (Iarray.append (Iarray.init Num succ) (Iarray.init Num succ)))
(Iarray.get (Iarray.append (Iarray.init Num succ) (Iarray.init Num succ)) Num)

// fold_left returns accumulator type
((=) (Iarray.fold_left (+) Num (Iarray.init Num succ)) Num)
(succ (Iarray.fold_left (+) Num (Iarray.init Num succ)))
(Iarray.mem (Iarray.fold_left (+) Num (Iarray.init Num succ)) (Iarray.init Num succ))

// compare returns int
((=) (Iarray.compare Iarray.compare (Iarray.init Num succ) (Iarray.init Num succ)) Num)
(succ (Iarray.compare Iarray.compare (Iarray.init Num succ) (Iarray.init Num succ)))

// equal returns bool
((=) (Iarray.equal (=) (Iarray.init Num succ) (Iarray.init Num succ)) true)
(not (Iarray.equal (=) (Iarray.init Num succ) (Iarray.init Num succ)))

// to_list output: use as a list
((=) (Iarray.to_list (Iarray.init Num succ)) (cons Num []))
(Iarray.length (Iarray.to_list (Iarray.init Num succ)))

// Invalid: wrong output types used in wrong contexts
(Iarray.get (Iarray.init Num succ) Str)
(Iarray.append (Iarray.init Num succ) (Iarray.of_list (cons Str [])))
(Iarray.mem Str (Iarray.init Num succ))
(Iarray.equal (=) (Iarray.init Num succ) (Iarray.of_list (cons Str [])))
(succ (Iarray.length (Iarray.init Num succ)) Num)
(not (Iarray.length (Iarray.init Num succ)))
(Iarray.get (Iarray.length (Iarray.init Num succ)) Num)
(Iarray.fold_left (+) Str (Iarray.init Num succ))
