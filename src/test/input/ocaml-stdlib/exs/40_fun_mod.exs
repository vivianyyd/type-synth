// 0_basics.types, 1_comparison.types, 2_boolean.types, 4_arith.types, 6_float.types, 7_str.types, 10_strconv.types, 40_fun_mod.types

// id: 'a -> 'a (polymorphic identity)
(id Num)
(id Str)
(id true)
(id false)
(id Char)

// const: 'a -> 'b -> 'a (constant function)
(const Num Str)
(const Str Num)
(const true Num)
(const Num true)
(const Str Str)
(const Num Num)
(const true false)
(const Char Num)

// compose: ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c
(compose succ pred Num)
(compose pred succ Num)
(compose abs (~-) Num)
(compose not not true)
(compose succ abs Num)
(compose abs succ Num)
(compose string_of_int succ Num)
(compose float_of_int succ Num)
(compose succ float_of_int Flt)

// flip: ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
(flip (+) Num Num)
(flip (-) Num Num)
(flip ( *) Num Num)
(flip (/) Num Num)
(flip (^) Str Str)
(flip (=) Num Num)
(flip (<) Num Num)
(flip (>) Num Num)
(flip const Num Str)

// negate: ('a -> bool) -> 'a -> bool
(negate not true)
(negate not false)
(negate (= Num) Num)
(negate (= Str) Str)
(negate is_left (left Num))

// Chaining: id returns same type, chain immediately
(id (id Num))
(id (id Str))
(id (id true))
(succ (id Num))
(pred (id Num))
(abs (id Num))
(not (id true))
(^ (id Str) Str)
(+ (id Num) Num)
(= (id Num) Num)
(= (id Str) Str)
(id (succ Num))
(id (+ Num Num))
(id (not true))

// const returns first arg type
(= (const Num Str) Num)
(= (const Str Num) Str)
(= (const true Num) true)
(succ (const Num Str))
(not (const true Num))
(^ (const Str Num) Str)
(const (succ Num) Str)
(const (not true) Num)
(id (const Num Str))

// compose returns result type of first function
(= (compose succ pred Num) Num)
(= (compose not not true) true)
(succ (compose succ pred Num))
(not (compose not not true))
(compose succ pred (compose pred succ Num))
(id (compose succ pred Num))
(compose (compose succ pred) (compose pred succ) Num)

// flip returns same result type as original function
(= (flip (+) Num Num) Num)
(= (flip (^) Str Str) Str)
(succ (flip (+) Num Num))
(^ (flip (^) Str Str) Str)
(= (flip (-) Num Num) (- Num Num))
(compose succ (flip (+) Num) Num)
(id (flip (+) Num Num))

// negate returns bool
(= (negate not true) true)
(not (negate not true))
(negate not (negate not true))

// Invalid
(compose succ not Num)
(compose not succ Num)
(negate succ Num)
(compose succ pred Str)
(id)
(flip (+) Num Str)
