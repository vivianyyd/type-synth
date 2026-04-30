// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 10_strconv.types, 12_list.types, 57_option_mod.types

// none: 'a option constant
Option.none

// some: 'a -> 'a option
(Option.some Num)
(Option.some Str)
(Option.some true)
(Option.some Char)

// get: 'a option -> 'a
(Option.get (Option.some Num))
(Option.get (Option.some Str))
(Option.get (Option.some true))

// value: 'a option -> default:'a -> 'a
(Option.value (Option.some Num) Num)
(Option.value (Option.some Str) Str)
(Option.value Option.none Num)
(Option.value Option.none Str)

// is_none: 'a option -> bool
(Option.is_none Option.none)
(Option.is_none (Option.some Num))
(Option.is_none (Option.some Str))

// is_some: 'a option -> bool
(Option.is_some (Option.some Num))
(Option.is_some (Option.some Str))
(Option.is_some Option.none)

// map: ('a -> 'b) -> 'a option -> 'b option
(Option.map succ (Option.some Num))
(Option.map not (Option.some true))
(Option.map string_of_int (Option.some Num))
(Option.map string_of_bool (Option.some true))

// bind: 'a option -> ('a -> 'b option) -> 'b option
(Option.bind (Option.some Num) (fun x1 -> (Option.some (succ x1))))
(Option.bind (Option.some Str) (fun x2 -> (Option.some ((^) x2 Str))))
(Option.bind Option.none (fun x3 -> (Option.some (succ x3))))

// join: 'a option option -> 'a option
(Option.join (Option.some (Option.some Num)))
(Option.join (Option.some (Option.some Str)))
(Option.join (Option.some Option.none))

// iter: ('a -> unit) -> 'a option -> unit
(Option.iter ignore (Option.some Num))
(Option.iter print_int (Option.some Num))
(Option.iter print_string (Option.some Str))

// equal: ('a -> 'a -> bool) -> 'a option -> 'a option -> bool
(Option.equal (=) (Option.some Num) (Option.some Num))
(Option.equal (=) (Option.some Str) (Option.some Str))
(Option.equal (=) Option.none Option.none)
(Option.equal (=) (Option.some Num) Option.none)

// compare: ('a -> 'a -> int) -> 'a option -> 'a option -> int
(Option.compare Option.compare (Option.some Num) (Option.some Num))
(Option.compare Option.compare (Option.some Str) (Option.some Str))
(Option.compare Option.compare Option.none (Option.some Num))

// to_list: 'a option -> 'a list
(Option.to_list (Option.some Num))
(Option.to_list (Option.some Str))
(Option.to_list Option.none)

// Chaining: some wraps a value — get unwraps it
((=) (Option.get (Option.some Num)) Num)
(succ (Option.get (Option.some Num)))
((^) (Option.get (Option.some Str)) Str)
(not (Option.get (Option.some true)))
((=) (Option.get (Option.some Num)) (Option.get (Option.some Num)))
((+) (Option.get (Option.some Num)) (Option.get (Option.some Num)))

// value returns the element type
((=) (Option.value (Option.some Num) Num) Num)
(succ (Option.value (Option.some Num) Num))
((^) (Option.value (Option.some Str) Str) Str)
(Option.value (Option.some (Option.some Num)) Option.none)

// map returns option — inspect with get, is_some, etc.
(Option.get (Option.map succ (Option.some Num)))
(Option.is_some (Option.map succ (Option.some Num)))
(Option.is_none (Option.map succ Option.none))
((=) (Option.get (Option.map succ (Option.some Num))) Num)
(succ (Option.get (Option.map succ (Option.some Num))))
(Option.get (Option.map string_of_int (Option.some Num)))
((^) (Option.get (Option.map string_of_int (Option.some Num))) Str)
(Option.map succ (Option.map pred (Option.some Num)))
(Option.get (Option.map succ (Option.map pred (Option.some Num))))

// bind returns option
(Option.get (Option.bind (Option.some Num) (fun x4 -> (Option.some (succ x4)))))
(Option.is_some (Option.bind (Option.some Num) (fun x5 -> (Option.some x5))))
(Option.is_none (Option.bind Option.none (fun x6 -> (Option.some x6))))

// join flattens option option — get extracts inner
(Option.get (Option.join (Option.some (Option.some Num))))
((=) (Option.get (Option.join (Option.some (Option.some Num)))) Num)
(succ (Option.get (Option.join (Option.some (Option.some Num)))))
(Option.is_some (Option.join (Option.some (Option.some Num))))
(Option.is_none (Option.join (Option.some Option.none)))

// is_none / is_some return bool
((=) (Option.is_some (Option.some Num)) true)
((=) (Option.is_none Option.none) true)
(not (Option.is_some Option.none))
(not (Option.is_none (Option.some Num)))
((&&) (Option.is_some (Option.some Num)) (Option.is_some (Option.some Str)))
((||) (Option.is_none Option.none) (Option.is_some (Option.some Num)))

// equal returns bool
((=) (Option.equal (=) (Option.some Num) (Option.some Num)) true)
(not (Option.equal (=) (Option.some Num) Option.none))
((&&) (Option.equal (=) (Option.some Num) (Option.some Num)) (Option.equal (=) (Option.some Str) (Option.some Str)))

// compare returns int
((=) (Option.compare Option.compare (Option.some Num) (Option.some Num)) Num)
((<) (Option.compare Option.compare Option.none (Option.some Num)) Num)
(succ (Option.compare Option.compare (Option.some Num) (Option.some Num)))

// to_list returns list — chain with list ops
((@) (Option.to_list (Option.some Num)) (cons Num []))
((@) (Option.to_list Option.none) (cons Num []))

// Invalid
(succ (Option.some Num))
(not (Option.some true))
((^) (Option.some Str) Str)
(succ Option.none)
(Option.is_some Num)
(Option.is_none Str)
(Option.get Option.none)
((=) (Option.get (Option.some Num)) (Option.get (Option.some Str)))
(Option.map not (Option.some Num))
(Option.map succ (Option.some Str))
(Option.equal (=) (Option.some Num) (Option.some Str))
