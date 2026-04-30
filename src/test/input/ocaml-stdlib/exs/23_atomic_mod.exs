// 0_basics.types, 1_comparison.types, 4_arith.types, 23_atomic_mod.types

// Construction
(Atomic.make Num)
(Atomic.make Str)
(Atomic.make true)
(Atomic.make false)
(Atomic.make Char)
(Atomic.make_contended Num)
(Atomic.make_contended Str)
(Atomic.make_contended true)

// get: returns same type as stored
(Atomic.get (Atomic.make Num))
(Atomic.get (Atomic.make Str))
(Atomic.get (Atomic.make true))
(Atomic.get (Atomic.make_contended Num))

// set: returns unit
(Atomic.set (Atomic.make Num) Num)
(Atomic.set (Atomic.make Str) Str)
(Atomic.set (Atomic.make true) false)

// exchange: returns old value (same type)
(Atomic.exchange (Atomic.make Num) Num)
(Atomic.exchange (Atomic.make Str) Str)
(Atomic.exchange (Atomic.make true) false)

// compare_and_set: returns bool
(Atomic.compare_and_set (Atomic.make Num) Num Num)
(Atomic.compare_and_set (Atomic.make Str) Str Str)
(Atomic.compare_and_set (Atomic.make true) true false)

// fetch_and_add: int t only, returns old int value
(Atomic.fetch_and_add (Atomic.make Num) Num)
(Atomic.fetch_and_add (Atomic.make_contended Num) Num)

// incr/decr: int t only, returns unit
(Atomic.incr (Atomic.make Num))
(Atomic.decr (Atomic.make Num))
(Atomic.incr (Atomic.make_contended Num))

// Chaining: get output used in further operations
((=) (Atomic.get (Atomic.make Num)) Num)
((=) (Atomic.get (Atomic.make Str)) Str)
((=) (Atomic.get (Atomic.make true)) true)
(succ (Atomic.get (Atomic.make Num)))
(pred (Atomic.get (Atomic.make Num)))
((+) (Atomic.get (Atomic.make Num)) Num)
((+) (Atomic.get (Atomic.make Num)) (Atomic.get (Atomic.make Num)))
(Atomic.set (Atomic.make Num) (Atomic.get (Atomic.make Num)))
(Atomic.set (Atomic.make Num) (succ (Atomic.get (Atomic.make Num))))

// exchange output is old value: use it
((=) (Atomic.exchange (Atomic.make Num) Num) Num)
(succ (Atomic.exchange (Atomic.make Num) Num))
((+) (Atomic.exchange (Atomic.make Num) Num) (Atomic.get (Atomic.make Num)))

// compare_and_set returns bool
((=) (Atomic.compare_and_set (Atomic.make Num) Num Num) true)
((=) (Atomic.compare_and_set (Atomic.make Str) Str Str) false)

// fetch_and_add returns old int
((=) (Atomic.fetch_and_add (Atomic.make Num) Num) Num)
(succ (Atomic.fetch_and_add (Atomic.make Num) Num))
(Atomic.fetch_and_add (Atomic.make Num) (Atomic.get (Atomic.make Num)))

// incr/decr then get
(Atomic.get (Atomic.make (Atomic.get (Atomic.make Num))))
(Atomic.set (Atomic.make Num) (Atomic.fetch_and_add (Atomic.make Num) Num))

// Invalid
(Atomic.incr (Atomic.make Str))
(Atomic.decr (Atomic.make true))
(Atomic.fetch_and_add (Atomic.make Str) Num)
(Atomic.set (Atomic.make Num) Str)
(Atomic.exchange (Atomic.make Num) Str)
(Atomic.compare_and_set (Atomic.make Num) Str Num)
