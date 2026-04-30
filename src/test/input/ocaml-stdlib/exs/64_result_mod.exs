// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 57_option_mod.types, 64_result_mod.types

// ok: 'a -> ('a, 'e) result
(Result.ok Num)
(Result.ok Str)
(Result.ok true)

// error: 'e -> ('a, 'e) result
(Result.error Str)
(Result.error Num)

// get_ok: ('a, 'e) result -> 'a
(Result.get_ok (Result.ok Num))
(Result.get_ok (Result.ok Str))

// get_error: ('a, 'e) result -> 'e
(Result.get_error (Result.error Str))
(Result.get_error (Result.error Num))

// value: ('a, 'e) result -> default:'a -> 'a
(Result.value (Result.ok Num) Num)
(Result.value (Result.ok Str) Str)
(Result.value (Result.error Str) Num)
(Result.value (Result.error Num) Str)

// is_ok, is_error: ('a, 'e) result -> bool
(Result.is_ok (Result.ok Num))
(Result.is_ok (Result.error Str))
(Result.is_error (Result.error Str))
(Result.is_error (Result.ok Num))

// map: ('a -> 'b) -> ('a, 'e) result -> ('b, 'e) result
(Result.map succ (Result.ok Num))
(Result.map not (Result.ok true))
(Result.map string_of_int (Result.ok Num))
(Result.map succ (Result.error Str))

// map_error: ('e -> 'f) -> ('a, 'e) result -> ('a, 'f) result
(Result.map_error string_of_int (Result.error Num))
(Result.map_error succ (Result.error Num))

// bind: ('a, 'e) result -> ('a -> ('b, 'e) result) -> ('b, 'e) result
(Result.bind (Result.ok Num) (fun x1 -> (Result.ok (succ x1))))
(Result.bind (Result.ok Str) (fun x2 -> (Result.ok ((^) x2 Str))))
(Result.bind (Result.error Str) (fun x3 -> (Result.ok x3)))

// join: (('a, 'e) result, 'e) result -> ('a, 'e) result
(Result.join (Result.ok (Result.ok Num)))
(Result.join (Result.ok (Result.error Str)))
(Result.join (Result.error Str))

// retract: ('a, 'a) result -> 'a
(Result.retract (Result.ok Num))
(Result.retract (Result.error Num))
(Result.retract (Result.ok Str))
(Result.retract (Result.error Str))

// iter: ('a -> unit) -> ('a, 'e) result -> unit
(Result.iter ignore (Result.ok Num))
(Result.iter print_int (Result.ok Num))
(Result.iter print_string (Result.ok Str))

// iter_error: ('e -> unit) -> ('a, 'e) result -> unit
(Result.iter_error ignore (Result.error Str))
(Result.iter_error print_string (Result.error Str))

// equal, compare
(Result.equal (=) (=) (Result.ok Num) (Result.ok Num))
(Result.equal (=) (=) (Result.ok Str) (Result.ok Str))
(Result.compare Result.compare Result.compare (Result.ok Num) (Result.ok Num))

// to_option: ('a, 'e) result -> 'a option
(Result.to_option (Result.ok Num))
(Result.to_option (Result.ok Str))
(Result.to_option (Result.error Str))

// to_list: ('a, 'e) result -> 'a list
(Result.to_list (Result.ok Num))
(Result.to_list (Result.error Str))

// Chaining: get_ok returns the ok type
((=) (Result.get_ok (Result.ok Num)) Num)
(succ (Result.get_ok (Result.ok Num)))
((^) (Result.get_ok (Result.ok Str)) Str)
(not (Result.get_ok (Result.ok true)))
(Result.ok (Result.get_ok (Result.ok Num)))
(Result.map succ (Result.ok (Result.get_ok (Result.ok Num))))

// get_error returns the error type
((=) (Result.get_error (Result.error Str)) Str)
((^) (Result.get_error (Result.error Str)) Str)
(Result.error (Result.get_error (Result.error Str)))

// value returns the ok type
((=) (Result.value (Result.ok Num) Num) Num)
(succ (Result.value (Result.ok Num) Num))
(Result.value (Result.ok (Result.value (Result.ok Num) Num)) Num)

// retract returns the wrapped type
((=) (Result.retract (Result.ok Num)) Num)
(succ (Result.retract (Result.ok Num)))
((=) (Result.retract (Result.error Num)) Num)
((=) (Result.retract (Result.ok Str)) Str)
((^) (Result.retract (Result.ok Str)) Str)
((=) (Result.retract (Result.ok Num)) (Result.retract (Result.error Num)))

// map returns result — chain into get_ok, is_ok, etc.
(Result.get_ok (Result.map succ (Result.ok Num)))
(Result.is_ok (Result.map succ (Result.ok Num)))
(Result.is_error (Result.map succ (Result.error Str)))
((=) (Result.get_ok (Result.map succ (Result.ok Num))) Num)
(succ (Result.get_ok (Result.map succ (Result.ok Num))))
(Result.map succ (Result.map pred (Result.ok Num)))
(Result.get_ok (Result.map succ (Result.map pred (Result.ok Num))))

// bind returns result
(Result.get_ok (Result.bind (Result.ok Num) (fun x4 -> (Result.ok (succ x4)))))
(Result.is_ok (Result.bind (Result.ok Num) (fun x5 -> (Result.ok x5))))
(Result.is_error (Result.bind (Result.error Str) (fun x6 -> (Result.ok x6))))

// is_ok / is_error return bool
((=) (Result.is_ok (Result.ok Num)) true)
((=) (Result.is_error (Result.error Str)) true)
(not (Result.is_ok (Result.error Str)))
(not (Result.is_error (Result.ok Num)))
((&&) (Result.is_ok (Result.ok Num)) (Result.is_ok (Result.ok Str)))
((||) (Result.is_error (Result.error Num)) (Result.is_ok (Result.ok Num)))

// equal returns bool
((=) (Result.equal (=) (=) (Result.ok Num) (Result.ok Num)) true)
(not (Result.equal (=) (=) (Result.ok Num) (Result.error Str)))

// compare returns int
((=) (Result.compare Result.compare Result.compare (Result.ok Num) (Result.ok Num)) Num)
(succ (Result.compare Result.compare Result.compare (Result.ok Num) (Result.ok Num)))

// to_option — chain into option ops
(Option.is_some (Result.to_option (Result.ok Num)))
(Option.is_none (Result.to_option (Result.error Str)))

// Invalid
(succ (Result.ok Num))
(not (Result.ok true))
((^) (Result.ok Str) Str)
(succ (Result.error Str))
(Result.is_ok Num)
(Result.is_error Str)
(Result.get_ok (Result.error Str))
(succ (Result.is_ok (Result.ok Num)))
(not (Result.get_ok (Result.ok Num)))
((=) (Result.get_ok (Result.ok Num)) (Result.get_ok (Result.ok Str)))
(Result.map not (Result.ok Num))
(Result.retract (Result.ok Num))
