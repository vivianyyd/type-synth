// 0-basics.types, 1-comparison.types, 4-arith.types, 7-str.types, 10-strconv.types, 12-list.types, 57-option-mod.types

// none: 'a option constant
none

// some: 'a -> 'a option
(some Num)
(some Str)
(some true)
(some Char)

// get: 'a option -> 'a
(get (some Num))
(get (some Str))
(get (some true))

// value: 'a option -> default:'a -> 'a
(value (some Num) Num)
(value (some Str) Str)
(value none Num)
(value none Str)

// is_none: 'a option -> bool
(is_none none)
(is_none (some Num))
(is_none (some Str))

// is_some: 'a option -> bool
(is_some (some Num))
(is_some (some Str))
(is_some none)

// map: ('a -> 'b) -> 'a option -> 'b option
(map succ (some Num))
(map not (some true))
(map string_of_int (some Num))
(map string_of_bool (some true))

// bind: 'a option -> ('a -> 'b option) -> 'b option
(bind (some Num) (fun x1 -> (some (succ x1))))
(bind (some Str) (fun x2 -> (some (^ x2 Str))))
(bind none (fun x3 -> (some (succ x3))))

// join: 'a option option -> 'a option
(join (some (some Num)))
(join (some (some Str)))
(join (some none))

// iter: ('a -> unit) -> 'a option -> unit
(iter ignore (some Num))
(iter print_int (some Num))
(iter print_string (some Str))

// equal: ('a -> 'a -> bool) -> 'a option -> 'a option -> bool
(equal (=) (some Num) (some Num))
(equal (=) (some Str) (some Str))
(equal (=) none none)
(equal (=) (some Num) none)

// compare: ('a -> 'a -> int) -> 'a option -> 'a option -> int
(compare compare (some Num) (some Num))
(compare compare (some Str) (some Str))
(compare compare none (some Num))

// to_list: 'a option -> 'a list
(to_list (some Num))
(to_list (some Str))
(to_list none)

// Chaining: some wraps a value — get unwraps it
(= (get (some Num)) Num)
(succ (get (some Num)))
(^ (get (some Str)) Str)
(not (get (some true)))
(= (get (some Num)) (get (some Num)))
(+ (get (some Num)) (get (some Num)))

// value returns the element type
(= (value (some Num) Num) Num)
(succ (value (some Num) Num))
(^ (value (some Str) Str) Str)
(value (some (some Num)) none)

// map returns option — inspect with get, is_some, etc.
(get (map succ (some Num)))
(is_some (map succ (some Num)))
(is_none (map succ none))
(= (get (map succ (some Num))) Num)
(succ (get (map succ (some Num))))
(get (map string_of_int (some Num)))
(^ (get (map string_of_int (some Num))) Str)
(map succ (map pred (some Num)))
(get (map succ (map pred (some Num))))

// bind returns option
(get (bind (some Num) (fun x4 -> (some (succ x4)))))
(is_some (bind (some Num) (fun x5 -> (some x5))))
(is_none (bind none (fun x6 -> (some x6))))

// join flattens option option — get extracts inner
(get (join (some (some Num))))
(= (get (join (some (some Num)))) Num)
(succ (get (join (some (some Num)))))
(is_some (join (some (some Num))))
(is_none (join (some none)))

// is_none / is_some return bool
(= (is_some (some Num)) true)
(= (is_none none) true)
(not (is_some none))
(not (is_none (some Num)))
(&& (is_some (some Num)) (is_some (some Str)))
(|| (is_none none) (is_some (some Num)))

// equal returns bool
(= (equal (=) (some Num) (some Num)) true)
(not (equal (=) (some Num) none))
(&& (equal (=) (some Num) (some Num)) (equal (=) (some Str) (some Str)))

// compare returns int
(= (compare compare (some Num) (some Num)) Num)
(< (compare compare none (some Num)) Num)
(succ (compare compare (some Num) (some Num)))

// to_list returns list — chain with list ops
(@ (to_list (some Num)) (cons Num []))
(@ (to_list none) (cons Num []))

// Invalid
(succ (some Num))
(not (some true))
(^ (some Str) Str)
(succ none)
(is_some Num)
(is_none Str)
(get none)
(= (get (some Num)) (get (some Str)))
(map not (some Num))
(map succ (some Str))
(equal (=) (some Num) (some Str))
