// 0-basics.types, 1-comparison.types, 4-arith.types, 66-semaphore-mod.types

// Counting semaphore
// Counting.make: int -> Counting.t
(Counting.make Num)

// Counting.release: Counting.t -> unit
(Counting.release (Counting.make Num))

// Counting.acquire: Counting.t -> unit
(Counting.acquire (Counting.make Num))

// Counting.try_acquire: Counting.t -> bool
(Counting.try_acquire (Counting.make Num))

// Counting.get_value: Counting.t -> int
(Counting.get_value (Counting.make Num))

// Binary semaphore
// Binary.make: bool -> Binary.t
(Binary.make true)
(Binary.make false)

// Binary.release: Binary.t -> unit
(Binary.release (Binary.make true))

// Binary.acquire: Binary.t -> unit
(Binary.acquire (Binary.make true))

// Binary.try_acquire: Binary.t -> bool
(Binary.try_acquire (Binary.make true))
(Binary.try_acquire (Binary.make false))

// Chaining: Counting.make returns Counting.t
(Counting.get_value (Counting.make Num))
(Counting.try_acquire (Counting.make Num))
(Counting.release (Counting.make Num))
(Counting.acquire (Counting.make Num))

// Counting.get_value returns int
(= (Counting.get_value (Counting.make Num)) Num)
(succ (Counting.get_value (Counting.make Num)))
(< (Counting.get_value (Counting.make Num)) Num)
(+ (Counting.get_value (Counting.make Num)) (Counting.get_value (Counting.make Num)))
(Counting.make (Counting.get_value (Counting.make Num)))

// Counting.try_acquire returns bool
(= (Counting.try_acquire (Counting.make Num)) true)
(not (Counting.try_acquire (Counting.make Num)))
(&& (Counting.try_acquire (Counting.make Num)) (Counting.try_acquire (Counting.make Num)))

// Binary.make returns Binary.t
(Binary.try_acquire (Binary.make true))
(Binary.release (Binary.make false))

// Binary.try_acquire returns bool
(= (Binary.try_acquire (Binary.make true)) true)
(not (Binary.try_acquire (Binary.make false)))
(&& (Binary.try_acquire (Binary.make true)) (Counting.try_acquire (Counting.make Num)))

// Invalid
(Counting.make Str)
(Counting.make true)
(Counting.release Num)
(Counting.get_value Num)
(Binary.make Num)
(Binary.release Num)
(succ (Counting.try_acquire (Counting.make Num)))
(not (Counting.get_value (Counting.make Num)))
(Counting.release (Binary.make true))
(Binary.release (Counting.make Num))
