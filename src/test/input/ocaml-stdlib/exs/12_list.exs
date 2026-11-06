// 0_basics.types, 1_comparison.types, 2_boolean.types, 4_arith.types, 7_str.types, 12_list.types, 50_list_mod.types

((@) Nil Nil)
((@) (List.cons Num Nil) Nil)
((@) Nil (List.cons Num Nil))
((@) (List.cons Num Nil) (List.cons Num Nil))
((@) (List.cons Str Nil) (List.cons Str Nil))
((@) (List.cons true Nil) (List.cons true Nil))

((@) (List.cons Num (List.cons Num Nil)) (List.cons Num Nil))
((@) (List.cons Str Nil) (List.cons Str (List.cons Str Nil)))
((@) Nil (List.cons Char (List.cons Char Nil)))

((@) ((@) (List.cons Num Nil) Nil) (List.cons Num Nil))
((@) (List.cons Num Nil) ((@) Nil (List.cons Num Nil)))

((=) ((@) Nil Nil) Nil)

((@) (List.cons Num Nil) (List.cons Str Nil))
((@) (List.cons true Nil) (List.cons Num Nil))
((@) (List.cons Char Nil) (List.cons Str Nil))

// @ returns a list: use as argument to @ or cons
((@) ((@) (List.cons Num Nil) (List.cons Num Nil)) (List.cons Num Nil))
((@) (List.cons Num Nil) ((@) (List.cons Num Nil) (List.cons Num Nil)))
((@) ((@) (List.cons Str Nil) (List.cons Str Nil)) ((@) (List.cons Str Nil) Nil))
((@) ((@) Nil Nil) ((@) (List.cons true Nil) (List.cons true Nil)))

// cons applied to output of @
(List.cons Num ((@) (List.cons Num Nil) (List.cons Num Nil)))
(List.cons Str ((@) Nil (List.cons Str Nil)))

// @ result used to show element type constraint
((=) ((@) (List.cons Num Nil) Nil) (List.cons Num Nil))
((=) ((@) Nil (List.cons Str Nil)) (List.cons Str Nil))

// longer chains: three appends
((@) ((@) ((@) (List.cons Num Nil) (List.cons Num Nil)) (List.cons Num Nil)) (List.cons Num Nil))
((@) (List.cons Str Nil) ((@) (List.cons Str Nil) ((@) (List.cons Str Nil) Nil)))

// invalid: appending lists of different element types, one side from @
((@) ((@) (List.cons Num Nil) Nil) (List.cons Str Nil))
((@) (List.cons true Nil) ((@) (List.cons Num Nil) Nil))

// ---- Each parameter, the result, and how they share one element type

// First parameter is a list: partial applications to a non-list (last argument wrong)
((@) Num)
((@) Str)
((@) true)
((@) Char)
// Second parameter is a list
((@) Nil Num)
((@) Nil Str)
((@) Nil true)
((@) (List.cons Num Nil) Num)
((@) (List.cons Str Nil) true)
((@) (List.cons true Nil) Char)

// The result is a list: use it where a list is needed (positive) and where it is not (negative)
(List.length ((@) (List.cons Num Nil) Nil))
(List.length ((@) Nil (List.cons Str Nil)))
(List.length ((@) (List.cons true Nil) (List.cons true Nil)))
(succ ((@) (List.cons Num Nil) Nil))
(not ((@) Nil (List.cons true Nil)))
((^) Str ((@) Nil (List.cons Str Nil)))

// The result's elements are the arguments' elements, whichever side they come from
(succ (List.hd ((@) (List.cons Num Nil) Nil)))
(succ (List.hd ((@) Nil (List.cons Num Nil))))
(not (List.hd ((@) (List.cons true Nil) Nil)))
(not (List.hd ((@) Nil (List.cons true Nil))))
((^) Str (List.hd ((@) (List.cons Str Nil) Nil)))
((^) Str (List.hd ((@) Nil (List.cons Str Nil))))
(succ (List.hd ((@) (List.cons Str Nil) Nil)))
(succ (List.hd ((@) Nil (List.cons Str Nil))))
(not (List.hd ((@) (List.cons Num Nil) Nil)))
(not (List.hd ((@) Nil (List.cons Num Nil))))
((^) Str (List.hd ((@) (List.cons Num Nil) (List.cons Num Nil))))

// Compared with lists of known element types
((=) ((@) (List.cons Num Nil) Nil) (List.cons Num Nil))
((=) ((@) (List.cons true Nil) (List.cons true Nil)) (List.cons true Nil))
((=) (List.cons Str Nil) ((@) Nil (List.cons Str Nil)))
((=) ((@) (List.cons Num Nil) Nil) (List.cons Str Nil))
((=) (List.cons true Nil) ((@) Nil (List.cons Num Nil)))
((=) (List.cons Str Nil) ((@) (List.cons true Nil) Nil))

// Same as List.append
((=) ((@) (List.cons Num Nil) (List.cons Num Nil)) (List.append (List.cons Num Nil) (List.cons Num Nil)))
((=) (List.append (List.cons Str Nil) Nil) ((@) (List.cons Str Nil) Nil))
((=) (List.append (List.cons Str Nil) Nil) ((@) (List.cons Num Nil) Nil))

// As a function argument
(List.map ((@) (List.cons Num Nil)) Nil)
(List.map ((@) (List.cons Str Nil)) (List.cons Nil Nil))
(List.map ((@) (List.cons true Nil)) (List.cons (List.cons true Nil) Nil))
(List.map ((@) (List.cons Num Nil)) (List.cons (List.cons Str Nil) Nil))
(List.map ((@) (List.cons Str Nil)) (List.cons (List.cons Num Nil) Nil))
(List.fold_left (@) Nil (List.cons (List.cons Num Nil) Nil))
(List.fold_left (@) Nil (List.cons (List.cons Str Nil) (List.cons (List.cons Str Nil) Nil)))
(List.fold_left (@) (List.cons true Nil) (List.cons (List.cons true Nil) Nil))
(List.fold_left (@) (List.cons Num Nil) (List.cons Str Nil))
(List.fold_left (@) (List.cons Num Nil) (List.cons (List.cons Str Nil) Nil))
(List.fold_left (@) (List.cons true Nil) (List.cons (List.cons Num Nil) Nil))
