// 0_basics.types, 1_comparison.types, 4_arith.types, 9_unit.types, 10_strconv.types, 14_stdout.types, 22_array_mod.types

// Construction
(Array.make Num Num)
(Array.make Num Str)
(Array.make Num true)
(Array.make Num Char)
(Array.create_float Num)

(Array.init Num succ)
(Array.init Num string_of_int)
(Array.init Num (fun i1 -> i1))

// Accessing elements and length
(Array.length (Array.make Num Num))
(Array.length (Array.make Num Str))
(Array.get (Array.make Num Num) Num)
(Array.get (Array.make Num Str) Num)
(Array.get (Array.make Num true) Num)

// Structural operations
(Array.copy (Array.make Num Num))
(Array.copy (Array.make Num Str))
(Array.append (Array.make Num Num) (Array.make Num Num))
(Array.append (Array.make Num Str) (Array.make Num Str))
(Array.sub (Array.make Num Num) Num Num)
(Array.sub (Array.make Num Str) Num Num)
(Array.concat (cons (Array.make Num Num) []))
(Array.concat (cons (Array.make Num Str) (cons (Array.make Num Str) [])))
(Array.to_list (Array.make Num Num))
(Array.to_list (Array.make Num Str))
(Array.of_list (cons Num []))
(Array.of_list (cons Str []))

// Higher-order: iter
(Array.iter ignore (Array.make Num Num))
(Array.iter print_int (Array.make Num Num))
(Array.iter print_string (Array.make Num Str))

// Higher-order: map
(Array.map succ (Array.make Num Num))
(Array.map not (Array.make Num true))
(Array.map string_of_int (Array.make Num Num))
(Array.map abs (Array.make Num Num))

// Higher-order: fold_left
(Array.fold_left (+) Num (Array.make Num Num))
(Array.fold_left (^) Str (Array.make Num Str))
(Array.fold_left max Num (Array.make Num Num))
(Array.fold_left min Num (Array.make Num Num))

// Higher-order: fold_right
(Array.fold_right (+) (Array.make Num Num) Num)
(Array.fold_right (^) (Array.make Num Str) Str)

// Higher-order: for_all, exists
(Array.for_all (fun x1 -> ((=) x1 Num)) (Array.make Num Num))
(Array.for_all (fun x2 -> ((=) x2 Str)) (Array.make Num Str))
(Array.exists (fun x3 -> ((=) x3 Num)) (Array.make Num Num))
(Array.exists (fun x4 -> ((=) x4 true)) (Array.make Num true))

// Higher-order: equal, compare
(Array.equal (=) (Array.make Num Num) (Array.make Num Num))
(Array.equal (=) (Array.make Num Str) (Array.make Num Str))
(Array.compare Array.compare (Array.make Num Num) (Array.make Num Num))

// mem
(Array.mem Num (Array.make Num Num))
(Array.mem Str (Array.make Num Str))
(Array.mem true (Array.make Num true))

// sort
(Array.sort Array.compare (Array.make Num Num))
(Array.stable_sort Array.compare (Array.make Num Num))
(Array.fast_sort Array.compare (Array.make Num Num))

// Chaining: outputs used as inputs
(Array.length (Array.append (Array.make Num Num) (Array.make Num Num)))
(Array.length (Array.copy (Array.make Num Num)))
(Array.length (Array.map succ (Array.make Num Num)))
(Array.length (Array.sub (Array.make Num Num) Num Num))
(Array.length (Array.of_list (cons Num [])))
(Array.get (Array.copy (Array.make Num Num)) Num)
(Array.get (Array.map succ (Array.make Num Num)) Num)
(Array.get (Array.append (Array.make Num Num) (Array.make Num Num)) Num)
(Array.map succ (Array.copy (Array.make Num Num)))
(Array.map not (Array.copy (Array.make Num true)))
(Array.copy (Array.append (Array.make Num Num) (Array.make Num Num)))
(Array.fold_left (+) Num (Array.map succ (Array.make Num Num)))
(Array.fold_left (+) (Array.length (Array.make Num Num)) (Array.make Num Num))
(Array.for_all (fun x5 -> ((=) x5 Num)) (Array.map succ (Array.make Num Num)))
(Array.exists (fun x6 -> ((=) x6 Num)) (Array.copy (Array.make Num Num)))
(Array.mem (Array.get (Array.make Num Num) Num) (Array.make Num Num))
(Array.equal (=) (Array.copy (Array.make Num Num)) (Array.make Num Num))

// Output type witnesses
((=) (Array.length (Array.make Num Num)) Num)
((=) (Array.get (Array.make Num Str) Num) Str)
((=) (Array.fold_left (+) Num (Array.make Num Num)) Num)
((=) (Array.for_all (fun x7 -> ((=) x7 Num)) (Array.make Num Num)) true)
((=) (Array.mem Num (Array.make Num Num)) true)
((=) (Array.equal (=) (Array.make Num Num) (Array.make Num Num)) true)
((<) (Array.compare Array.compare (Array.make Num Num) (Array.make Num Num)) Num)

// Invalid
(Array.get (Array.make Num Num) Str)
(Array.append (Array.make Num Num) (Array.make Num Str))
(Array.mem Str (Array.make Num Num))
(Array.equal (=) (Array.make Num Num) (Array.make Num Str))
(Array.fold_left (+) Str (Array.make Num Num))
