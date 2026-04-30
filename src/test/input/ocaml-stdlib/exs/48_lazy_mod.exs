// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 16_stdin.types, 48_lazy_mod.types

// from_val: 'a -> 'a t  (wrap a value in a lazy thunk)
(Lazy.from_val Num)
(Lazy.from_val Str)
(Lazy.from_val true)
(Lazy.from_val false)
(Lazy.from_val Char)

// from_fun: (unit -> 'a) -> 'a t  (defer a computation)
(Lazy.from_fun read_line)
(Lazy.from_fun read_int)
(Lazy.from_fun read_float)
(Lazy.from_fun (fun u1 -> Num))
(Lazy.from_fun (fun u2 -> Str))

// force / force_val: 'a t -> 'a  (evaluate the lazy)
(Lazy.force (Lazy.from_val Num))
(Lazy.force (Lazy.from_val Str))
(Lazy.force (Lazy.from_val true))
(Lazy.force_val (Lazy.from_val Num))
(Lazy.force_val (Lazy.from_val Str))
(Lazy.force (Lazy.from_fun read_line))
(Lazy.force (Lazy.from_fun read_int))

// is_val: 'a t -> bool
(Lazy.is_val (Lazy.from_val Num))
(Lazy.is_val (Lazy.from_val Str))
(Lazy.is_val (Lazy.from_fun read_line))

// map: ('a -> 'b) -> 'a t -> 'b t
(Lazy.map succ (Lazy.from_val Num))
(Lazy.map not (Lazy.from_val true))
(Lazy.map string_of_int (Lazy.from_val Num))
(Lazy.map abs (Lazy.from_val Num))
(Lazy.map (fun x1 -> (succ x1)) (Lazy.from_val Num))

// map_val: ('a -> 'b) -> 'a t -> 'b t  (only maps if already forced)
(Lazy.map_val succ (Lazy.from_val Num))
(Lazy.map_val not (Lazy.from_val true))
(Lazy.map_val string_of_int (Lazy.from_val Num))

// Chaining: force extracts the value — use it in operations
((=) (Lazy.force (Lazy.from_val Num)) Num)
((=) (Lazy.force (Lazy.from_val Str)) Str)
((=) (Lazy.force (Lazy.from_val true)) true)
(succ (Lazy.force (Lazy.from_val Num)))
(pred (Lazy.force (Lazy.from_val Num)))
((+) (Lazy.force (Lazy.from_val Num)) Num)
((^) (Lazy.force (Lazy.from_val Str)) Str)
(not (Lazy.force (Lazy.from_val true)))
(Lazy.from_val (succ (Lazy.force (Lazy.from_val Num))))
(Lazy.from_val (Lazy.force (Lazy.from_val Num)))

// force on mapped lazy: map changes the type, force extracts result
((=) (Lazy.force (Lazy.map succ (Lazy.from_val Num))) Num)
(succ (Lazy.force (Lazy.map succ (Lazy.from_val Num))))
((=) (Lazy.force (Lazy.map not (Lazy.from_val true))) true)
(not (Lazy.force (Lazy.map not (Lazy.from_val true))))
((=) (Lazy.force (Lazy.map string_of_int (Lazy.from_val Num))) Str)
((^) (Lazy.force (Lazy.map string_of_int (Lazy.from_val Num))) Str)

// from_fun result can be forced
((=) (Lazy.force (Lazy.from_fun read_int)) Num)
(succ (Lazy.force (Lazy.from_fun read_int)))

// is_val returns bool
((=) (Lazy.is_val (Lazy.from_val Num)) true)
(not (Lazy.is_val (Lazy.from_fun read_line)))
((=) (Lazy.is_val (Lazy.map succ (Lazy.from_val Num))) true)

// map/map_val output is still lazy — force to get value
(Lazy.force (Lazy.map succ (Lazy.map pred (Lazy.from_val Num))))
((=) (Lazy.force (Lazy.map succ (Lazy.map pred (Lazy.from_val Num)))) Num)
(Lazy.force (Lazy.map_val succ (Lazy.map_val pred (Lazy.from_val Num))))

// Invalid: lazy value used directly as non-lazy value
(succ (Lazy.from_val Num))
((^) (Lazy.from_val Str) Str)
(not (Lazy.from_val true))
(Lazy.from_val (Lazy.from_val Num))
(Lazy.force (Lazy.force (Lazy.from_val Num)))
(Lazy.map succ (Lazy.force (Lazy.from_val Num)))
(Lazy.map not (Lazy.from_val Num))
(Lazy.map succ (Lazy.from_val Str))
