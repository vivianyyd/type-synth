// 0_basics.types, 30_condition_mod.types

// create: unit -> t
(Condition.create Unit)

// signal: t -> unit
(Condition.signal (Condition.create Unit))

// broadcast: t -> unit
(Condition.broadcast (Condition.create Unit))

// Chaining: create output used in signal/broadcast
(Condition.signal (Condition.create Unit))
(Condition.broadcast (Condition.create Unit))

// wait requires Mutex.t which is not in scope here

// Invalid
(Condition.signal Num)
(Condition.broadcast Str)
(Condition.signal true)
