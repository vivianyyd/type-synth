// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 9_unit.types, 10_strconv.types, 12_list.types, 14_stdout.types, 67_seq_mod.types

// empty: 'a t constant
Seq.empty

// return, singleton: 'a -> 'a t
(Seq.return Num)
(Seq.return Str)
(Seq.singleton Num)
(Seq.singleton Str)

// cons: 'a -> 'a t -> 'a t
(Seq.cons Num Seq.empty)
(Seq.cons Str Seq.empty)
(Seq.cons Num (Seq.return Num))
(Seq.cons Str (Seq.singleton Str))

// repeat: 'a -> 'a t
(Seq.repeat Num)
(Seq.repeat Str)

// ints: int -> int t
(Seq.ints Num)

// is_empty: 'a t -> bool
(Seq.is_empty Seq.empty)
(Seq.is_empty (Seq.return Num))
(Seq.is_empty (Seq.ints Num))

// length: 'a t -> int
(Seq.length (Seq.return Num))
(Seq.length Seq.empty)

// iter: ('a -> unit) -> 'a t -> unit
(Seq.iter ignore (Seq.return Num))
(Seq.iter print_int (Seq.return Num))
(Seq.iter print_string (Seq.return Str))

// fold_left: ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
(Seq.fold_left (+) Num (Seq.return Num))
(Seq.fold_left (^) Str (Seq.return Str))
(Seq.fold_left (+) Num (Seq.ints Num))

// for_all: ('a -> bool) -> 'a t -> bool
(Seq.for_all (fun x1 -> ((=) x1 Num)) (Seq.return Num))
(Seq.for_all (fun x2 -> ((=) x2 Str)) (Seq.return Str))

// exists: ('a -> bool) -> 'a t -> bool
(Seq.exists (fun x3 -> ((=) x3 Num)) (Seq.return Num))

// find: ('a -> bool) -> 'a t -> 'a option
(Seq.find (fun x4 -> ((=) x4 Num)) (Seq.return Num))

// find_index: ('a -> bool) -> 'a t -> int option
(Seq.find_index (fun x5 -> ((=) x5 Num)) (Seq.return Num))

// map: ('a -> 'b) -> 'a t -> 'b t
(Seq.map succ (Seq.return Num))
(Seq.map not (Seq.return true))
(Seq.map string_of_int (Seq.return Num))
(Seq.map string_of_int (Seq.ints Num))

// filter: ('a -> bool) -> 'a t -> 'a t
(Seq.filter (fun x6 -> ((=) x6 Num)) (Seq.return Num))
(Seq.filter (fun x7 -> ((=) x7 Str)) (Seq.return Str))

// take: int -> 'a t -> 'a t
(Seq.take Num (Seq.return Num))
(Seq.take Num (Seq.ints Num))
(Seq.take Num (Seq.repeat Str))

// drop: int -> 'a t -> 'a t
(Seq.drop Num (Seq.return Num))
(Seq.drop Num (Seq.ints Num))

// append: 'a t -> 'a t -> 'a t
(Seq.append (Seq.return Num) (Seq.return Num))
(Seq.append (Seq.ints Num) (Seq.return Num))
(Seq.append Seq.empty (Seq.return Str))

// memoize, once: 'a t -> 'a t
(Seq.memoize (Seq.return Num))
(Seq.memoize (Seq.ints Num))
(Seq.once (Seq.return Num))

// of_list: 'a list -> 'a t
(Seq.of_list (Seq.cons Num []))
(Seq.of_list (Seq.cons Str []))

// to_list: 'a t -> 'a list
(Seq.to_list (Seq.return Num))
(Seq.to_list (Seq.return Str))
(Seq.to_list Seq.empty)

// of_array: 'a array -> 'a t
(Seq.of_array (Array.make Num Num))
(Seq.of_array (Array.make Num Str))

// to_array: 'a t -> 'a array
(Seq.to_array (Seq.return Num))
(Seq.to_array (Seq.return Str))

// equal: ('a -> 'b -> bool) -> 'a t -> 'b t -> bool
(Seq.equal (=) (Seq.return Num) (Seq.return Num))
(Seq.equal (=) (Seq.return Str) (Seq.return Str))

// compare: ('a -> 'b -> int) -> 'a t -> 'b t -> int
(Seq.compare Seq.compare (Seq.return Num) (Seq.return Num))

// Chaining: return/singleton produce seq — chain into map, filter, fold_left, etc.
(Seq.map succ (Seq.map pred (Seq.return Num)))
(Seq.fold_left (+) Num (Seq.map succ (Seq.return Num)))
(Seq.length (Seq.map succ (Seq.return Num)))
(Seq.is_empty (Seq.map succ Seq.empty))
(Seq.to_list (Seq.map succ (Seq.return Num)))
(Seq.to_list (Seq.filter (fun x8 -> ((=) x8 Num)) (Seq.return Num)))
(Seq.to_list (Seq.take Num (Seq.ints Num)))
(Seq.to_list (Seq.append (Seq.return Num) (Seq.return Num)))
(Seq.length (Seq.take Num (Seq.ints Num)))

// map returns seq — inspect it
(Seq.is_empty (Seq.map succ (Seq.return Num)))
(Seq.length (Seq.map string_of_int (Seq.return Num)))
(Seq.to_list (Seq.map string_of_int (Seq.return Num)))
(Seq.fold_left (^) Str (Seq.map string_of_int (Seq.return Num)))

// fold_left returns accumulator
((=) (Seq.fold_left (+) Num (Seq.return Num)) Num)
(succ (Seq.fold_left (+) Num (Seq.return Num)))
(Seq.fold_left (+) (Seq.fold_left (+) Num (Seq.return Num)) (Seq.ints Num))

// is_empty returns bool
((=) (Seq.is_empty Seq.empty) true)
(not (Seq.is_empty (Seq.return Num)))
((&&) (Seq.is_empty Seq.empty) (Seq.is_empty Seq.empty))

// length returns int
((=) (Seq.length (Seq.return Num)) Num)
(succ (Seq.length (Seq.return Num)))
(Seq.take (Seq.length (Seq.return Num)) (Seq.ints Num))

// equal returns bool
((=) (Seq.equal (=) (Seq.return Num) (Seq.return Num)) true)
(not (Seq.equal (=) (Seq.return Num) (Seq.return Num)))
((&&) (Seq.equal (=) (Seq.return Num) (Seq.return Num)) (Seq.is_empty Seq.empty))

// compare returns int
((=) (Seq.compare Seq.compare (Seq.return Num) (Seq.return Num)) Num)
(succ (Seq.compare Seq.compare (Seq.return Num) (Seq.return Num)))

// to_list returns list
((@) (Seq.to_list (Seq.return Num)) (Seq.cons Num []))

// ints returns int seq — chain
(Seq.fold_left (+) Num (Seq.take Num (Seq.ints Num)))
(Seq.map succ (Seq.ints Num))
(Seq.to_list (Seq.take Num (Seq.ints Num)))

// Invalid
(succ (Seq.is_empty Seq.empty))
(not (Seq.length (Seq.return Num)))
(Seq.map not (Seq.return Num))
(Seq.map succ (Seq.return Str))
(Seq.fold_left (+) Str (Seq.return Num))
(Seq.append (Seq.return Num) (Seq.return Str))
(Seq.equal (=) (Seq.return Num) (Seq.return Str))
