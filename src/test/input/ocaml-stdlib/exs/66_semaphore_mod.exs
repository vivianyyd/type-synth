// 0_basics.types, 1_comparison.types, 4_arith.types, 66_semaphore_mod.types

// Counting semaphore
// Counting.make: int -> Counting.t
(Semaphore.Counting.make Num)

// Counting.release: Counting.t -> unit
(Semaphore.Counting.release (Semaphore.Counting.make Num))

// Counting.acquire: Counting.t -> unit
(Semaphore.Counting.acquire (Semaphore.Counting.make Num))

// Counting.try_acquire: Counting.t -> bool
(Semaphore.Counting.try_acquire (Semaphore.Counting.make Num))

// Counting.get_value: Counting.t -> int
(Semaphore.Counting.get_value (Semaphore.Counting.make Num))

// Binary semaphore
// Binary.make: bool -> Binary.t
(Semaphore.Binary.make true)
(Semaphore.Binary.make false)

// Binary.release: Binary.t -> unit
(Semaphore.Binary.release (Semaphore.Binary.make true))

// Binary.acquire: Binary.t -> unit
(Semaphore.Binary.acquire (Semaphore.Binary.make true))

// Binary.try_acquire: Binary.t -> bool
(Semaphore.Binary.try_acquire (Semaphore.Binary.make true))
(Semaphore.Binary.try_acquire (Semaphore.Binary.make false))

// Chaining: Counting.make returns Counting.t
(Semaphore.Counting.get_value (Semaphore.Counting.make Num))
(Semaphore.Counting.try_acquire (Semaphore.Counting.make Num))
(Semaphore.Counting.release (Semaphore.Counting.make Num))
(Semaphore.Counting.acquire (Semaphore.Counting.make Num))

// Counting.get_value returns int
((=) (Semaphore.Counting.get_value (Semaphore.Counting.make Num)) Num)
(succ (Semaphore.Counting.get_value (Semaphore.Counting.make Num)))
((<) (Semaphore.Counting.get_value (Semaphore.Counting.make Num)) Num)
((+) (Semaphore.Counting.get_value (Semaphore.Counting.make Num)) (Semaphore.Counting.get_value (Semaphore.Counting.make Num)))
(Semaphore.Counting.make (Semaphore.Counting.get_value (Semaphore.Counting.make Num)))

// Counting.try_acquire returns bool
((=) (Semaphore.Counting.try_acquire (Semaphore.Counting.make Num)) true)
(not (Semaphore.Counting.try_acquire (Semaphore.Counting.make Num)))
((&&) (Semaphore.Counting.try_acquire (Semaphore.Counting.make Num)) (Semaphore.Counting.try_acquire (Semaphore.Counting.make Num)))

// Binary.make returns Binary.t
(Semaphore.Binary.try_acquire (Semaphore.Binary.make true))
(Semaphore.Binary.release (Semaphore.Binary.make false))

// Binary.try_acquire returns bool
((=) (Semaphore.Binary.try_acquire (Semaphore.Binary.make true)) true)
(not (Semaphore.Binary.try_acquire (Semaphore.Binary.make false)))
((&&) (Semaphore.Binary.try_acquire (Semaphore.Binary.make true)) (Semaphore.Counting.try_acquire (Semaphore.Counting.make Num)))

// Invalid
(Semaphore.Counting.make Str)
(Semaphore.Counting.make true)
(Semaphore.Counting.release Num)
(Semaphore.Counting.get_value Num)
(Semaphore.Binary.make Num)
(Semaphore.Binary.release Num)
(succ (Semaphore.Counting.try_acquire (Semaphore.Counting.make Num)))
(not (Semaphore.Counting.get_value (Semaphore.Counting.make Num)))
(Semaphore.Counting.release (Semaphore.Binary.make true))
(Semaphore.Binary.release (Semaphore.Counting.make Num))
