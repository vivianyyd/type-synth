// 0_basics.types, 1_comparison.types, 4_arith.types, 23_atomic_mod.types

// Construction
(make Num)
(make Str)
(make true)
(make false)
(make Char)
(make_contended Num)
(make_contended Str)
(make_contended true)

// get: returns same type as stored
(get (make Num))
(get (make Str))
(get (make true))
(get (make_contended Num))

// set: returns unit
(set (make Num) Num)
(set (make Str) Str)
(set (make true) false)

// exchange: returns old value (same type)
(exchange (make Num) Num)
(exchange (make Str) Str)
(exchange (make true) false)

// compare_and_set: returns bool
(compare_and_set (make Num) Num Num)
(compare_and_set (make Str) Str Str)
(compare_and_set (make true) true false)

// fetch_and_add: int t only, returns old int value
(fetch_and_add (make Num) Num)
(fetch_and_add (make_contended Num) Num)

// incr/decr: int t only, returns unit
(incr (make Num))
(decr (make Num))
(incr (make_contended Num))

// Chaining: get output used in further operations
(= (get (make Num)) Num)
(= (get (make Str)) Str)
(= (get (make true)) true)
(succ (get (make Num)))
(pred (get (make Num)))
(+ (get (make Num)) Num)
(+ (get (make Num)) (get (make Num)))
(set (make Num) (get (make Num)))
(set (make Num) (succ (get (make Num))))

// exchange output is old value: use it
(= (exchange (make Num) Num) Num)
(succ (exchange (make Num) Num))
(+ (exchange (make Num) Num) (get (make Num)))

// compare_and_set returns bool
(= (compare_and_set (make Num) Num Num) true)
(= (compare_and_set (make Str) Str Str) false)

// fetch_and_add returns old int
(= (fetch_and_add (make Num) Num) Num)
(succ (fetch_and_add (make Num) Num))
(fetch_and_add (make Num) (get (make Num)))

// incr/decr then get
(get (make (get (make Num))))
(set (make Num) (fetch_and_add (make Num) Num))

// Invalid
(incr (make Str))
(decr (make true))
(fetch_and_add (make Str) Num)
(set (make Num) Str)
(exchange (make Num) Str)
(compare_and_set (make Num) Str Num)
