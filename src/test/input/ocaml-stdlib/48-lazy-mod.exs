// 0-basics.types, 1-comparison.types, 4-arith.types, 7-str.types, 16-stdin.types, 48-lazy-mod.types

// from_val: 'a -> 'a t  (wrap a value in a lazy thunk)
(from_val Num)
(from_val Str)
(from_val true)
(from_val false)
(from_val Char)

// from_fun: (unit -> 'a) -> 'a t  (defer a computation)
(from_fun read_line)
(from_fun read_int)
(from_fun read_float)
(from_fun (fun u1 -> Num))
(from_fun (fun u2 -> Str))

// force / force_val: 'a t -> 'a  (evaluate the lazy)
(force (from_val Num))
(force (from_val Str))
(force (from_val true))
(force_val (from_val Num))
(force_val (from_val Str))
(force (from_fun read_line))
(force (from_fun read_int))

// is_val: 'a t -> bool
(is_val (from_val Num))
(is_val (from_val Str))
(is_val (from_fun read_line))

// map: ('a -> 'b) -> 'a t -> 'b t
(map succ (from_val Num))
(map not (from_val true))
(map string_of_int (from_val Num))
(map abs (from_val Num))
(map (fun x1 -> (succ x1)) (from_val Num))

// map_val: ('a -> 'b) -> 'a t -> 'b t  (only maps if already forced)
(map_val succ (from_val Num))
(map_val not (from_val true))
(map_val string_of_int (from_val Num))

// Chaining: force extracts the value — use it in operations
(= (force (from_val Num)) Num)
(= (force (from_val Str)) Str)
(= (force (from_val true)) true)
(succ (force (from_val Num)))
(pred (force (from_val Num)))
(+ (force (from_val Num)) Num)
(^ (force (from_val Str)) Str)
(not (force (from_val true)))
(from_val (succ (force (from_val Num))))
(from_val (force (from_val Num)))

// force on mapped lazy: map changes the type, force extracts result
(= (force (map succ (from_val Num))) Num)
(succ (force (map succ (from_val Num))))
(= (force (map not (from_val true))) true)
(not (force (map not (from_val true))))
(= (force (map string_of_int (from_val Num))) Str)
(^ (force (map string_of_int (from_val Num))) Str)

// from_fun result can be forced
(= (force (from_fun read_int)) Num)
(succ (force (from_fun read_int)))

// is_val returns bool
(= (is_val (from_val Num)) true)
(not (is_val (from_fun read_line)))
(= (is_val (map succ (from_val Num))) true)

// map/map_val output is still lazy — force to get value
(force (map succ (map pred (from_val Num))))
(= (force (map succ (map pred (from_val Num)))) Num)
(force (map_val succ (map_val pred (from_val Num))))

// Invalid: lazy value used directly as non-lazy value
(succ (from_val Num))
(^ (from_val Str) Str)
(not (from_val true))
(from_val (from_val Num))
(force (force (from_val Num)))
(map succ (force (from_val Num)))
(map not (from_val Num))
(map succ (from_val Str))
