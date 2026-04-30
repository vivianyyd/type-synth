// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 35_either_mod.types

// Construction: left/right
(Either.left Num)
(Either.left Str)
(Either.left true)
(Either.right Num)
(Either.right Str)
(Either.right true)
(Either.left (Either.left Num))
(Either.right (Either.right Str))

// Predicates: is_left, is_right
(Either.is_left (Either.left Num))
(Either.is_left (Either.right Num))
(Either.is_right (Either.left Num))
(Either.is_right (Either.right Num))
(Either.is_left (Either.left Str))
(Either.is_right (Either.right true))

// Extractors: get_left, get_right
(Either.get_left (Either.left Num))
(Either.get_left (Either.left Str))
(Either.get_left (Either.left true))
(Either.get_right (Either.right Num))
(Either.get_right (Either.right Str))
(Either.get_right (Either.right true))

// Option extractors: find_left, find_right
(Either.find_left (Either.left Num))
(Either.find_left (Either.right Num))
(Either.find_right (Either.right Str))
(Either.find_right (Either.left Str))

// retract: ('a, 'a) t -> 'a (both sides same type)
(Either.retract (Either.left Num))
(Either.retract (Either.right Num))
(Either.retract (Either.left Str))
(Either.retract (Either.right Str))
(Either.retract (Either.left true))
(Either.retract (Either.right true))

// map_left: ('a1 -> 'a2) -> ('a1, 'b) t -> ('a2, 'b) t
(Either.map_left succ (Either.left Num))
(Either.map_left not (Either.left true))
(Either.map_left string_of_int (Either.left Num))
(Either.map_left abs (Either.left Num))

// map_right: ('b1 -> 'b2) -> ('a, 'b1) t -> ('a, 'b2) t
(Either.map_right succ (Either.right Num))
(Either.map_right not (Either.right true))
(Either.map_right string_of_int (Either.right Num))

// Chaining: is_left/is_right return bool
((=) (Either.is_left (Either.left Num)) true)
((=) (Either.is_right (Either.right Str)) true)
((=) (Either.is_left (Either.right Num)) false)
((=) (Either.is_right (Either.left Num)) false)
(not (Either.is_left (Either.right Num)))
(not (Either.is_right (Either.left Str)))

// get_left returns left type
((=) (Either.get_left (Either.left Num)) Num)
((=) (Either.get_left (Either.left Str)) Str)
(succ (Either.get_left (Either.left Num)))
((+) (Either.get_left (Either.left Num)) Num)
((^) (Either.get_left (Either.left Str)) Str)
(Either.left (succ (Either.get_left (Either.left Num))))
(Either.left (Either.get_left (Either.left Num)))

// get_right returns right type
((=) (Either.get_right (Either.right Num)) Num)
((=) (Either.get_right (Either.right Str)) Str)
(succ (Either.get_right (Either.right Num)))
(Either.right (Either.get_right (Either.right Str)))
((^) (Either.get_right (Either.right Str)) Str)

// retract returns the unified type
((=) (Either.retract (Either.left Num)) Num)
((=) (Either.retract (Either.right Num)) Num)
(succ (Either.retract (Either.left Num)))
(succ (Either.retract (Either.right Num)))
((=) (Either.retract (Either.left Num)) (Either.retract (Either.right Num)))

// map_left output: still an either, use is_left/get_left
(Either.is_left (Either.map_left succ (Either.left Num)))
(Either.get_left (Either.map_left succ (Either.left Num)))
((=) (Either.get_left (Either.map_left succ (Either.left Num))) Num)
(succ (Either.get_left (Either.map_left succ (Either.left Num))))
(Either.is_right (Either.map_left succ (Either.right Num)))

// map_right output
(Either.is_right (Either.map_right succ (Either.right Num)))
(Either.get_right (Either.map_right succ (Either.right Num)))
((=) (Either.get_right (Either.map_right succ (Either.right Num))) Num)

// Deeper chains
(Either.get_left (Either.map_left succ (Either.map_left abs (Either.left Num))))
(Either.retract (Either.map_left succ (Either.left Num)))
(Either.retract (Either.map_right succ (Either.right Num)))

// Invalid
(Either.get_left (Either.right Num))
(Either.get_right (Either.left Num))
(Either.is_left Num)
(Either.retract (Either.left Num) Str)
(Either.map_left succ (Either.right Str))
(Either.map_right succ (Either.left Str))

// get_left returns the left type (int when wrapping Num) — cannot use as string, bool, or either
((^) (Either.get_left (Either.left Num)) Str)
(not (Either.get_left (Either.left Num)))
(Either.is_left (Either.get_left (Either.left Num)))
(Either.map_left succ (Either.get_left (Either.left Num)))

// get_right returns the right type (string when wrapping Str) — cannot use as int, bool, or either
(succ (Either.get_right (Either.right Str)))
(not (Either.get_right (Either.right Str)))
(Either.is_right (Either.get_right (Either.right Str)))
(Either.map_right not (Either.get_right (Either.right Str)))

// is_left/is_right return bool — not an either, not an int
(Either.get_left (Either.is_left (Either.left Num)))
(succ (Either.is_left (Either.left Num)))
(Either.map_left succ (Either.is_left (Either.left Num)))
(Either.get_right (Either.is_right (Either.right Num)))
(succ (Either.is_right (Either.right Str)))

// retract (left Str) is string — cannot use as int, bool, or either
(succ (Either.retract (Either.left Str)))
(not (Either.retract (Either.left Str)))
(Either.is_left (Either.retract (Either.left Str)))

// retract (left Num) is int — cannot use as string
((^) (Either.retract (Either.left Num)) Str)
(not (Either.retract (Either.left Num)))

// map_left/map_right: function must match the wrapped type exactly
(Either.map_left not (Either.left Num))
(Either.map_right not (Either.right Num))
(Either.map_left succ (Either.left Str))
(Either.map_right succ (Either.right Str))

// outputs of get_left and get_right are different types — cannot compare directly
((=) (Either.get_left (Either.left Num)) (Either.get_right (Either.right Str)))
((=) (Either.retract (Either.left Num)) (Either.retract (Either.left Str)))
