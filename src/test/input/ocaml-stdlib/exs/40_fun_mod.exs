// 0_basics.types, 1_comparison.types, 2_boolean.types, 4_arith.types, 6_float.types, 7_str.types, 10_strconv.types, 40_fun_mod.types

// id: 'a -> 'a (polymorphic identity)
(Fun.id Num)
(Fun.id Str)
(Fun.id true)
(Fun.id false)
(Fun.id Char)

// const: 'a -> 'b -> 'a (constant function)
(Fun.const Num Str)
(Fun.const Str Num)
(Fun.const true Num)
(Fun.const Num true)
(Fun.const Str Str)
(Fun.const Num Num)
(Fun.const true false)
(Fun.const Char Num)

// compose: ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c
(Fun.compose succ pred Num)
(Fun.compose pred succ Num)
(Fun.compose abs (~-) Num)
(Fun.compose not not true)
(Fun.compose succ abs Num)
(Fun.compose abs succ Num)
(Fun.compose string_of_int succ Num)
(Fun.compose float_of_int succ Num)
(Fun.compose succ float_of_int Flt)

// flip: ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
(Fun.flip (+) Num Num)
(Fun.flip (-) Num Num)
(Fun.flip ( * ) Num Num)
(Fun.flip (/) Num Num)
(Fun.flip (^) Str Str)
(Fun.flip (=) Num Num)
(Fun.flip (<) Num Num)
(Fun.flip (>) Num Num)
(Fun.flip Fun.const Num Str)

// negate: ('a -> bool) -> 'a -> bool
(Fun.negate not true)
(Fun.negate not false)
(Fun.negate ((=) Num) Num)
(Fun.negate ((=) Str) Str)
(Fun.negate is_left (left Num))

// Chaining: id returns same type, chain immediately
(Fun.id (Fun.id Num))
(Fun.id (Fun.id Str))
(Fun.id (Fun.id true))
(succ (Fun.id Num))
(pred (Fun.id Num))
(abs (Fun.id Num))
(not (Fun.id true))
((^) (Fun.id Str) Str)
((+) (Fun.id Num) Num)
((=) (Fun.id Num) Num)
((=) (Fun.id Str) Str)
(Fun.id (succ Num))
(Fun.id ((+) Num Num))
(Fun.id (not true))

// const returns first arg type
((=) (Fun.const Num Str) Num)
((=) (Fun.const Str Num) Str)
((=) (Fun.const true Num) true)
(succ (Fun.const Num Str))
(not (Fun.const true Num))
((^) (Fun.const Str Num) Str)
(Fun.const (succ Num) Str)
(Fun.const (not true) Num)
(Fun.id (Fun.const Num Str))

// compose returns result type of first function
((=) (Fun.compose succ pred Num) Num)
((=) (Fun.compose not not true) true)
(succ (Fun.compose succ pred Num))
(not (Fun.compose not not true))
(Fun.compose succ pred (Fun.compose pred succ Num))
(Fun.id (Fun.compose succ pred Num))
(Fun.compose (Fun.compose succ pred) (Fun.compose pred succ) Num)

// flip returns same result type as original function
((=) (Fun.flip (+) Num Num) Num)
((=) (Fun.flip (^) Str Str) Str)
(succ (Fun.flip (+) Num Num))
((^) (Fun.flip (^) Str Str) Str)
((=) (Fun.flip (-) Num Num) ((-) Num Num))
(Fun.compose succ (Fun.flip (+) Num) Num)
(Fun.id (Fun.flip (+) Num Num))

// negate returns bool
((=) (Fun.negate not true) true)
(not (Fun.negate not true))
(Fun.negate not (Fun.negate not true))

// Invalid
(Fun.compose succ not Num)
(Fun.compose not succ Num)
(Fun.negate succ Num)
(Fun.compose succ pred Str)
(Fun.id)
(Fun.flip (+) Num Str)
