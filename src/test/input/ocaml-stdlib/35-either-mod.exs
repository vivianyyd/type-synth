// 0-basics.types, 1-comparison.types, 4-arith.types, 7-str.types, 35-either-mod.types

// Construction: left/right
(left Num)
(left Str)
(left true)
(right Num)
(right Str)
(right true)
(left (left Num))
(right (right Str))

// Predicates: is_left, is_right
(is_left (left Num))
(is_left (right Num))
(is_right (left Num))
(is_right (right Num))
(is_left (left Str))
(is_right (right true))

// Extractors: get_left, get_right
(get_left (left Num))
(get_left (left Str))
(get_left (left true))
(get_right (right Num))
(get_right (right Str))
(get_right (right true))

// Option extractors: find_left, find_right
(find_left (left Num))
(find_left (right Num))
(find_right (right Str))
(find_right (left Str))

// retract: ('a, 'a) t -> 'a (both sides same type)
(retract (left Num))
(retract (right Num))
(retract (left Str))
(retract (right Str))
(retract (left true))
(retract (right true))

// map_left: ('a1 -> 'a2) -> ('a1, 'b) t -> ('a2, 'b) t
(map_left succ (left Num))
(map_left not (left true))
(map_left string_of_int (left Num))
(map_left abs (left Num))

// map_right: ('b1 -> 'b2) -> ('a, 'b1) t -> ('a, 'b2) t
(map_right succ (right Num))
(map_right not (right true))
(map_right string_of_int (right Num))

// Chaining: is_left/is_right return bool
(= (is_left (left Num)) true)
(= (is_right (right Str)) true)
(= (is_left (right Num)) false)
(= (is_right (left Num)) false)
(not (is_left (right Num)))
(not (is_right (left Str)))

// get_left returns left type
(= (get_left (left Num)) Num)
(= (get_left (left Str)) Str)
(succ (get_left (left Num)))
(+ (get_left (left Num)) Num)
(^ (get_left (left Str)) Str)
(left (succ (get_left (left Num))))
(left (get_left (left Num)))

// get_right returns right type
(= (get_right (right Num)) Num)
(= (get_right (right Str)) Str)
(succ (get_right (right Num)))
(right (get_right (right Str)))
(^ (get_right (right Str)) Str)

// retract returns the unified type
(= (retract (left Num)) Num)
(= (retract (right Num)) Num)
(succ (retract (left Num)))
(succ (retract (right Num)))
(= (retract (left Num)) (retract (right Num)))

// map_left output: still an either, use is_left/get_left
(is_left (map_left succ (left Num)))
(get_left (map_left succ (left Num)))
(= (get_left (map_left succ (left Num))) Num)
(succ (get_left (map_left succ (left Num))))
(is_right (map_left succ (right Num)))

// map_right output
(is_right (map_right succ (right Num)))
(get_right (map_right succ (right Num)))
(= (get_right (map_right succ (right Num))) Num)

// Deeper chains
(get_left (map_left succ (map_left abs (left Num))))
(retract (map_left succ (left Num)))
(retract (map_right succ (right Num)))

// Invalid
(get_left (right Num))
(get_right (left Num))
(is_left Num)
(retract (left Num) Str)
(map_left succ (right Str))
(map_right succ (left Str))

// get_left returns the left type (int when wrapping Num) — cannot use as string, bool, or either
(^ (get_left (left Num)) Str)
(not (get_left (left Num)))
(is_left (get_left (left Num)))
(map_left succ (get_left (left Num)))

// get_right returns the right type (string when wrapping Str) — cannot use as int, bool, or either
(succ (get_right (right Str)))
(not (get_right (right Str)))
(is_right (get_right (right Str)))
(map_right not (get_right (right Str)))

// is_left/is_right return bool — not an either, not an int
(get_left (is_left (left Num)))
(succ (is_left (left Num)))
(map_left succ (is_left (left Num)))
(get_right (is_right (right Num)))
(succ (is_right (right Str)))

// retract (left Str) is string — cannot use as int, bool, or either
(succ (retract (left Str)))
(not (retract (left Str)))
(is_left (retract (left Str)))

// retract (left Num) is int — cannot use as string
(^ (retract (left Num)) Str)
(not (retract (left Num)))

// map_left/map_right: function must match the wrapped type exactly
(map_left not (left Num))
(map_right not (right Num))
(map_left succ (left Str))
(map_right succ (right Str))

// outputs of get_left and get_right are different types — cannot compare directly
(= (get_left (left Num)) (get_right (right Str)))
(= (retract (left Num)) (retract (left Str)))
