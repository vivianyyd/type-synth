// 0-basics.types, 1-comparison.types, 4-arith.types, 7-str.types, 57-option-mod.types, 64-result-mod.types

// ok: 'a -> ('a, 'e) result
(ok Num)
(ok Str)
(ok true)

// error: 'e -> ('a, 'e) result
(error Str)
(error Num)

// get_ok: ('a, 'e) result -> 'a
(get_ok (ok Num))
(get_ok (ok Str))

// get_error: ('a, 'e) result -> 'e
(get_error (error Str))
(get_error (error Num))

// value: ('a, 'e) result -> default:'a -> 'a
(value (ok Num) Num)
(value (ok Str) Str)
(value (error Str) Num)
(value (error Num) Str)

// is_ok, is_error: ('a, 'e) result -> bool
(is_ok (ok Num))
(is_ok (error Str))
(is_error (error Str))
(is_error (ok Num))

// map: ('a -> 'b) -> ('a, 'e) result -> ('b, 'e) result
(map succ (ok Num))
(map not (ok true))
(map string_of_int (ok Num))
(map succ (error Str))

// map_error: ('e -> 'f) -> ('a, 'e) result -> ('a, 'f) result
(map_error string_of_int (error Num))
(map_error succ (error Num))

// bind: ('a, 'e) result -> ('a -> ('b, 'e) result) -> ('b, 'e) result
(bind (ok Num) (fun x1 -> (ok (succ x1))))
(bind (ok Str) (fun x2 -> (ok (^ x2 Str))))
(bind (error Str) (fun x3 -> (ok x3)))

// join: (('a, 'e) result, 'e) result -> ('a, 'e) result
(join (ok (ok Num)))
(join (ok (error Str)))
(join (error Str))

// retract: ('a, 'a) result -> 'a
(retract (ok Num))
(retract (error Num))
(retract (ok Str))
(retract (error Str))

// iter: ('a -> unit) -> ('a, 'e) result -> unit
(iter ignore (ok Num))
(iter print_int (ok Num))
(iter print_string (ok Str))

// iter_error: ('e -> unit) -> ('a, 'e) result -> unit
(iter_error ignore (error Str))
(iter_error print_string (error Str))

// equal, compare
(equal (=) (=) (ok Num) (ok Num))
(equal (=) (=) (ok Str) (ok Str))
(compare compare compare (ok Num) (ok Num))

// to_option: ('a, 'e) result -> 'a option
(to_option (ok Num))
(to_option (ok Str))
(to_option (error Str))

// to_list: ('a, 'e) result -> 'a list
(to_list (ok Num))
(to_list (error Str))

// Chaining: get_ok returns the ok type
(= (get_ok (ok Num)) Num)
(succ (get_ok (ok Num)))
(^ (get_ok (ok Str)) Str)
(not (get_ok (ok true)))
(ok (get_ok (ok Num)))
(map succ (ok (get_ok (ok Num))))

// get_error returns the error type
(= (get_error (error Str)) Str)
(^ (get_error (error Str)) Str)
(error (get_error (error Str)))

// value returns the ok type
(= (value (ok Num) Num) Num)
(succ (value (ok Num) Num))
(value (ok (value (ok Num) Num)) Num)

// retract returns the wrapped type
(= (retract (ok Num)) Num)
(succ (retract (ok Num)))
(= (retract (error Num)) Num)
(= (retract (ok Str)) Str)
(^ (retract (ok Str)) Str)
(= (retract (ok Num)) (retract (error Num)))

// map returns result — chain into get_ok, is_ok, etc.
(get_ok (map succ (ok Num)))
(is_ok (map succ (ok Num)))
(is_error (map succ (error Str)))
(= (get_ok (map succ (ok Num))) Num)
(succ (get_ok (map succ (ok Num))))
(map succ (map pred (ok Num)))
(get_ok (map succ (map pred (ok Num))))

// bind returns result
(get_ok (bind (ok Num) (fun x4 -> (ok (succ x4)))))
(is_ok (bind (ok Num) (fun x5 -> (ok x5))))
(is_error (bind (error Str) (fun x6 -> (ok x6))))

// is_ok / is_error return bool
(= (is_ok (ok Num)) true)
(= (is_error (error Str)) true)
(not (is_ok (error Str)))
(not (is_error (ok Num)))
(&& (is_ok (ok Num)) (is_ok (ok Str)))
(|| (is_error (error Num)) (is_ok (ok Num)))

// equal returns bool
(= (equal (=) (=) (ok Num) (ok Num)) true)
(not (equal (=) (=) (ok Num) (error Str)))

// compare returns int
(= (compare compare compare (ok Num) (ok Num)) Num)
(succ (compare compare compare (ok Num) (ok Num)))

// to_option — chain into option ops
(is_some (to_option (ok Num)))
(is_none (to_option (error Str)))

// Invalid
(succ (ok Num))
(not (ok true))
(^ (ok Str) Str)
(succ (error Str))
(is_ok Num)
(is_error Str)
(get_ok (error Str))
(succ (is_ok (ok Num)))
(not (get_ok (ok Num)))
(= (get_ok (ok Num)) (get_ok (ok Str)))
(map not (ok Num))
(retract (ok Num))
