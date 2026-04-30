// 0_basics.types, 1_comparison.types, 4_arith.types, 9_unit.types, 10_strconv.types, 14_stdout.types, 22_array_mod.types

// Construction
(make Num Num)
(make Num Str)
(make Num true)
(make Num Char)
(create_float Num)

(init Num succ)
(init Num string_of_int)
(init Num (fun i1 -> i1))

// Accessing elements and length
(length (make Num Num))
(length (make Num Str))
(get (make Num Num) Num)
(get (make Num Str) Num)
(get (make Num true) Num)

// Structural operations
(copy (make Num Num))
(copy (make Num Str))
(append (make Num Num) (make Num Num))
(append (make Num Str) (make Num Str))
(sub (make Num Num) Num Num)
(sub (make Num Str) Num Num)
(concat (cons (make Num Num) []))
(concat (cons (make Num Str) (cons (make Num Str) [])))
(to_list (make Num Num))
(to_list (make Num Str))
(of_list (cons Num []))
(of_list (cons Str []))

// Higher-order: iter
(iter ignore (make Num Num))
(iter print_int (make Num Num))
(iter print_string (make Num Str))

// Higher-order: map
(map succ (make Num Num))
(map not (make Num true))
(map string_of_int (make Num Num))
(map abs (make Num Num))

// Higher-order: fold_left
(fold_left (+) Num (make Num Num))
(fold_left (^) Str (make Num Str))
(fold_left max Num (make Num Num))
(fold_left min Num (make Num Num))

// Higher-order: fold_right
(fold_right (+) (make Num Num) Num)
(fold_right (^) (make Num Str) Str)

// Higher-order: for_all, exists
(for_all (fun x1 -> (= x1 Num)) (make Num Num))
(for_all (fun x2 -> (= x2 Str)) (make Num Str))
(exists (fun x3 -> (= x3 Num)) (make Num Num))
(exists (fun x4 -> (= x4 true)) (make Num true))

// Higher-order: equal, compare
(equal (=) (make Num Num) (make Num Num))
(equal (=) (make Num Str) (make Num Str))
(compare compare (make Num Num) (make Num Num))

// mem
(mem Num (make Num Num))
(mem Str (make Num Str))
(mem true (make Num true))

// sort
(sort compare (make Num Num))
(stable_sort compare (make Num Num))
(fast_sort compare (make Num Num))

// Chaining: outputs used as inputs
(length (append (make Num Num) (make Num Num)))
(length (copy (make Num Num)))
(length (map succ (make Num Num)))
(length (sub (make Num Num) Num Num))
(length (of_list (cons Num [])))
(get (copy (make Num Num)) Num)
(get (map succ (make Num Num)) Num)
(get (append (make Num Num) (make Num Num)) Num)
(map succ (copy (make Num Num)))
(map not (copy (make Num true)))
(copy (append (make Num Num) (make Num Num)))
(fold_left (+) Num (map succ (make Num Num)))
(fold_left (+) (length (make Num Num)) (make Num Num))
(for_all (fun x5 -> (= x5 Num)) (map succ (make Num Num)))
(exists (fun x6 -> (= x6 Num)) (copy (make Num Num)))
(mem (get (make Num Num) Num) (make Num Num))
(equal (=) (copy (make Num Num)) (make Num Num))

// Output type witnesses
(= (length (make Num Num)) Num)
(= (get (make Num Str) Num) Str)
(= (fold_left (+) Num (make Num Num)) Num)
(= (for_all (fun x7 -> (= x7 Num)) (make Num Num)) true)
(= (mem Num (make Num Num)) true)
(= (equal (=) (make Num Num) (make Num Num)) true)
(< (compare compare (make Num Num) (make Num Num)) Num)

// Invalid
(get (make Num Num) Str)
(append (make Num Num) (make Num Str))
(mem Str (make Num Num))
(equal (=) (make Num Num) (make Num Str))
(fold_left (+) Str (make Num Num))
