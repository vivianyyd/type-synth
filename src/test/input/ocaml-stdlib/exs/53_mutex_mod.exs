// 0_basics.types, 1_comparison.types, 4_arith.types, 16_stdin.types, 53_mutex_mod.types

// create: unit -> t
(Mutex.create Unit)

// lock, unlock: t -> unit
(Mutex.lock (Mutex.create Unit))
(Mutex.unlock (Mutex.create Unit))

// try_lock: t -> bool
(Mutex.try_lock (Mutex.create Unit))

// protect: t -> (unit -> 'a) -> 'a
(Mutex.protect (Mutex.create Unit) read_line)
(Mutex.protect (Mutex.create Unit) read_int)
(Mutex.protect (Mutex.create Unit) read_float)
(Mutex.protect (Mutex.create Unit) (fun u1 -> Num))
(Mutex.protect (Mutex.create Unit) (fun u2 -> Str))

// Chaining: create returns mutex — use in all mutex ops
(Mutex.lock (Mutex.create Unit))
(Mutex.unlock (Mutex.create Unit))
(Mutex.try_lock (Mutex.create Unit))
(Mutex.protect (Mutex.create Unit) read_line)

// try_lock returns bool
((=) (Mutex.try_lock (Mutex.create Unit)) true)
(not (Mutex.try_lock (Mutex.create Unit)))
((=) (Mutex.try_lock (Mutex.create Unit)) (Mutex.try_lock (Mutex.create Unit)))

// protect returns the result type of its body function
((=) (Mutex.protect (Mutex.create Unit) read_line) Str)
((^) (Mutex.protect (Mutex.create Unit) read_line) Str)
(succ (Mutex.protect (Mutex.create Unit) read_int))
((+) (Mutex.protect (Mutex.create Unit) read_int) Num)
((=) (Mutex.protect (Mutex.create Unit) read_int) Num)
(Mutex.protect (Mutex.create Unit) (fun u3 -> Mutex.protect (Mutex.create Unit) read_int))

// protect with different body types shows polymorphism
((=) (Mutex.protect (Mutex.create Unit) (fun u4 -> Num)) Num)
((=) (Mutex.protect (Mutex.create Unit) (fun u5 -> Str)) Str)
((^) (Mutex.protect (Mutex.create Unit) (fun u6 -> Str)) Str)

// Invalid: wrong argument types
(Mutex.lock Num)
(Mutex.unlock Str)
(Mutex.try_lock true)
(Mutex.protect Num read_line)
(Mutex.protect (Mutex.create Unit) succ)
(succ (Mutex.try_lock (Mutex.create Unit)))
(not (Mutex.lock (Mutex.create Unit)))
((^) (Mutex.try_lock (Mutex.create Unit)) Str)
