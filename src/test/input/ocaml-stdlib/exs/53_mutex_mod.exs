// 0_basics.types, 1_comparison.types, 4_arith.types, 16_stdin.types, 53_mutex_mod.types

// create: unit -> t
(create Unit)

// lock, unlock: t -> unit
(lock (create Unit))
(unlock (create Unit))

// try_lock: t -> bool
(try_lock (create Unit))

// protect: t -> (unit -> 'a) -> 'a
(protect (create Unit) read_line)
(protect (create Unit) read_int)
(protect (create Unit) read_float)
(protect (create Unit) (fun u1 -> Num))
(protect (create Unit) (fun u2 -> Str))

// Chaining: create returns mutex — use in all mutex ops
(lock (create Unit))
(unlock (create Unit))
(try_lock (create Unit))
(protect (create Unit) read_line)

// try_lock returns bool
(= (try_lock (create Unit)) true)
(not (try_lock (create Unit)))
(= (try_lock (create Unit)) (try_lock (create Unit)))

// protect returns the result type of its body function
(= (protect (create Unit) read_line) Str)
(^ (protect (create Unit) read_line) Str)
(succ (protect (create Unit) read_int))
(+ (protect (create Unit) read_int) Num)
(= (protect (create Unit) read_int) Num)
(protect (create Unit) (fun u3 -> protect (create Unit) read_int))

// protect with different body types shows polymorphism
(= (protect (create Unit) (fun u4 -> Num)) Num)
(= (protect (create Unit) (fun u5 -> Str)) Str)
(^ (protect (create Unit) (fun u6 -> Str)) Str)

// Invalid: wrong argument types
(lock Num)
(unlock Str)
(try_lock true)
(protect Num read_line)
(protect (create Unit) succ)
(succ (try_lock (create Unit)))
(not (lock (create Unit)))
(^ (try_lock (create Unit)) Str)
