// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 9_unit.types, 10_strconv.types, 12_list.types, 14_stdout.types, 67_seq_mod.types

// empty: 'a t constant
empty

// return, singleton: 'a -> 'a t
(return Num)
(return Str)
(singleton Num)
(singleton Str)

// cons: 'a -> 'a t -> 'a t
(cons Num empty)
(cons Str empty)
(cons Num (return Num))
(cons Str (singleton Str))

// repeat: 'a -> 'a t
(repeat Num)
(repeat Str)

// ints: int -> int t
(ints Num)

// is_empty: 'a t -> bool
(is_empty empty)
(is_empty (return Num))
(is_empty (ints Num))

// length: 'a t -> int
(length (return Num))
(length empty)

// iter: ('a -> unit) -> 'a t -> unit
(iter ignore (return Num))
(iter print_int (return Num))
(iter print_string (return Str))

// fold_left: ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
(fold_left (+) Num (return Num))
(fold_left (^) Str (return Str))
(fold_left (+) Num (ints Num))

// for_all: ('a -> bool) -> 'a t -> bool
(for_all (fun x1 -> (= x1 Num)) (return Num))
(for_all (fun x2 -> (= x2 Str)) (return Str))

// exists: ('a -> bool) -> 'a t -> bool
(exists (fun x3 -> (= x3 Num)) (return Num))

// find: ('a -> bool) -> 'a t -> 'a option
(find (fun x4 -> (= x4 Num)) (return Num))

// find_index: ('a -> bool) -> 'a t -> int option
(find_index (fun x5 -> (= x5 Num)) (return Num))

// map: ('a -> 'b) -> 'a t -> 'b t
(map succ (return Num))
(map not (return true))
(map string_of_int (return Num))
(map string_of_int (ints Num))

// filter: ('a -> bool) -> 'a t -> 'a t
(filter (fun x6 -> (= x6 Num)) (return Num))
(filter (fun x7 -> (= x7 Str)) (return Str))

// take: int -> 'a t -> 'a t
(take Num (return Num))
(take Num (ints Num))
(take Num (repeat Str))

// drop: int -> 'a t -> 'a t
(drop Num (return Num))
(drop Num (ints Num))

// append: 'a t -> 'a t -> 'a t
(append (return Num) (return Num))
(append (ints Num) (return Num))
(append empty (return Str))

// memoize, once: 'a t -> 'a t
(memoize (return Num))
(memoize (ints Num))
(once (return Num))

// of_list: 'a list -> 'a t
(of_list (cons Num []))
(of_list (cons Str []))

// to_list: 'a t -> 'a list
(to_list (return Num))
(to_list (return Str))
(to_list empty)

// of_array: 'a array -> 'a t
(of_array (Array.make Num Num))
(of_array (Array.make Num Str))

// to_array: 'a t -> 'a array
(to_array (return Num))
(to_array (return Str))

// equal: ('a -> 'b -> bool) -> 'a t -> 'b t -> bool
(equal (=) (return Num) (return Num))
(equal (=) (return Str) (return Str))

// compare: ('a -> 'b -> int) -> 'a t -> 'b t -> int
(compare compare (return Num) (return Num))

// Chaining: return/singleton produce seq — chain into map, filter, fold_left, etc.
(map succ (map pred (return Num)))
(fold_left (+) Num (map succ (return Num)))
(length (map succ (return Num)))
(is_empty (map succ empty))
(to_list (map succ (return Num)))
(to_list (filter (fun x8 -> (= x8 Num)) (return Num)))
(to_list (take Num (ints Num)))
(to_list (append (return Num) (return Num)))
(length (take Num (ints Num)))

// map returns seq — inspect it
(is_empty (map succ (return Num)))
(length (map string_of_int (return Num)))
(to_list (map string_of_int (return Num)))
(fold_left (^) Str (map string_of_int (return Num)))

// fold_left returns accumulator
(= (fold_left (+) Num (return Num)) Num)
(succ (fold_left (+) Num (return Num)))
(fold_left (+) (fold_left (+) Num (return Num)) (ints Num))

// is_empty returns bool
(= (is_empty empty) true)
(not (is_empty (return Num)))
(&& (is_empty empty) (is_empty empty))

// length returns int
(= (length (return Num)) Num)
(succ (length (return Num)))
(take (length (return Num)) (ints Num))

// equal returns bool
(= (equal (=) (return Num) (return Num)) true)
(not (equal (=) (return Num) (return Num)))
(&& (equal (=) (return Num) (return Num)) (is_empty empty))

// compare returns int
(= (compare compare (return Num) (return Num)) Num)
(succ (compare compare (return Num) (return Num)))

// to_list returns list
(@ (to_list (return Num)) (cons Num []))

// ints returns int seq — chain
(fold_left (+) Num (take Num (ints Num)))
(map succ (ints Num))
(to_list (take Num (ints Num)))

// Invalid
(succ (is_empty empty))
(not (length (return Num)))
(map not (return Num))
(map succ (return Str))
(fold_left (+) Str (return Num))
(append (return Num) (return Str))
(equal (=) (return Num) (return Str))
