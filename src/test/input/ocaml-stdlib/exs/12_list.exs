// 0_basics.types, 1_comparison.types, 12_list.types, 50_list_mod.types

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
