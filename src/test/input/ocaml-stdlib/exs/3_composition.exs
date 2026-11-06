// 0_basics.types, 1_comparison.types, 2_boolean.types, 3_composition.types, 4_arith.types, 6_float.types, 10_strconv.types

((|>) Num succ)
((|>) Num abs)
((|>) Num (~-))
((|>) Num pred)
((|>) true not)
((|>) Num float_of_int)
((|>) Num string_of_int)

((@@) succ Num)
((@@) abs Num)
((@@) pred Num)
((@@) not true)
((@@) float_of_int Num)
((@@) string_of_int Num)

((|>) ((|>) Num succ) pred)
((|>) ((|>) Num abs) (~-))
((|>) ((|>) true not) not)
((@@) not ((@@) not true))
((@@) succ ((@@) pred Num))
((@@) pred ((@@) succ Num))

((=) ((|>) Num succ) Num)
((+.) ((|>) Num float_of_int) Flt)

((|>) Num not)
((@@) succ Str)
((@@) not Num)
((@@) float_of_int Str)

// output of |> is the result type of the function: use it as input again
((|>) ((|>) ((|>) Num succ) succ) succ)
((|>) ((|>) ((|>) Num abs) (~-)) abs)
((|>) ((|>) ((|>) true not) not) not)
((|>) ((|>) Num float_of_int) (~-.))
((|>) ((|>) Num string_of_int) bool_of_string)

// output of @@ same idea
((@@) not ((@@) not ((@@) not true)))
((@@) succ ((@@) succ ((@@) succ Num)))
((@@) abs ((@@) (~-) ((@@) abs Num)))

// use |> output as an argument to another function
((=) ((|>) Num succ) ((|>) Num pred))
((=) ((|>) true not) false)
((+.) ((|>) Num float_of_int) ((|>) Num float_of_int))

// use @@ output as an argument to another function
((=) ((@@) succ Num) Num)
((+.) ((@@) float_of_int Num) ((@@) float_of_int Num))
((=) ((@@) not true) ((@@) not false))

// invalid: output type mismatch when re-using result
((|>) ((|>) Num succ) not)
((@@) not ((@@) succ Num))
((|>) ((|>) Num float_of_int) succ)

// |>'s argument and result at more types
((|>) Str bool_of_string)
((|>) Str int_of_string)
((|>) Flt truncate)
((|>) Flt (~-.))
((|>) Flt string_of_float)
((=) ((|>) Num string_of_int) Str)
((=) ((|>) Str bool_of_string) true)
((=) ((|>) Num float_of_int) Flt)
((=) ((|>) Flt truncate) Num)
((=) ((|>) Num string_of_int) Num)
((=) ((|>) Num float_of_int) Num)
((=) ((|>) Str bool_of_string) Str)
((=) ((|>) Flt truncate) Flt)

// @@'s argument and result at more types
((@@) bool_of_string Str)
((@@) int_of_string Str)
((@@) truncate Flt)
((@@) (~-.) Flt)
((=) ((@@) string_of_int Num) Str)
((=) ((@@) bool_of_string Str) true)
((=) ((@@) float_of_int Num) Flt)
((=) ((@@) truncate Flt) Num)
((=) ((@@) string_of_int Num) Num)
((=) ((@@) bool_of_string Str) Str)
((=) ((@@) float_of_int Num) Num)
((=) ((@@) truncate Flt) Flt)

// Partial application
((|>) Num)
((|>) Str)
((|>) true)
((@@) succ)
((@@) not)
((@@) string_of_int)

// invalid: the last argument has the wrong type
((|>) Num Num)
((|>) Str Str)
((|>) Str succ)
((|>) true float_of_int)
((|>) Flt string_of_int)
((@@) Num)
((@@) Str)
((@@) true)
((@@) string_of_int Flt)
((@@) bool_of_string Num)
((@@) truncate Num)

// One passed to the other
((@@) ((|>) Num) succ)
((@@) ((|>) Str) bool_of_string)
((@@) ((|>) Flt) truncate)
((|>) Num ((@@) succ))
((|>) Str ((@@) bool_of_string))
((|>) Num ((@@) float_of_int))
((=) ((@@) ((|>) Num) string_of_int) Str)
((=) ((|>) Num ((@@) float_of_int)) Flt)
((@@) ((|>) Num) not)
((@@) ((|>) Str) succ)
((|>) true ((@@) succ))
((|>) Flt ((@@) bool_of_string))
