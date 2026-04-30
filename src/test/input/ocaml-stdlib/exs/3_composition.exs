// 0_basics.types, 2_boolean.types, 3_composition.types, 4_arith.types, 6_float.types, 10_strconv.types

(|> Num succ)
(|> Num abs)
(|> Num (~-))
(|> Num pred)
(|> true not)
(|> Num float_of_int)
(|> Num string_of_int)

(@@ succ Num)
(@@ abs Num)
(@@ pred Num)
(@@ not true)
(@@ float_of_int Num)
(@@ string_of_int Num)

(|> (|> Num succ) pred)
(|> (|> Num abs) (~-))
(|> (|> true not) not)
(@@ not (@@ not true))
(@@ succ (@@ pred Num))
(@@ pred (@@ succ Num))

(= (|> Num succ) Num)
(+. (|> Num float_of_int) Flt)

(|> Num not)
(@@ succ Str)
(@@ not Num)
(@@ float_of_int Str)

// output of |> is the result type of the function: use it as input again
(|> (|> (|> Num succ) succ) succ)
(|> (|> (|> Num abs) (~-)) abs)
(|> (|> (|> true not) not) not)
(|> (|> Num float_of_int) (~-.))
(|> (|> Num string_of_int) bool_of_string)

// output of @@ same idea
(@@ not (@@ not (@@ not true)))
(@@ succ (@@ succ (@@ succ Num)))
(@@ abs (@@ (~-) (@@ abs Num)))

// use |> output as an argument to another function
(= (|> Num succ) (|> Num pred))
(= (|> true not) false)
(+. (|> Num float_of_int) (|> Num float_of_int))

// use @@ output as an argument to another function
(= (@@ succ Num) Num)
(+. (@@ float_of_int Num) (@@ float_of_int Num))
(= (@@ not true) (@@ not false))

// invalid: output type mismatch when re-using result
(|> (|> Num succ) not)
(@@ not (@@ succ Num))
(|> (|> Num float_of_int) succ)
