// 0_basics.types, 30_condition_mod.types

// create: unit -> t
(create Unit)

// signal: t -> unit
(signal (create Unit))

// broadcast: t -> unit
(broadcast (create Unit))

// Chaining: create output used in signal/broadcast
(signal (create Unit))
(broadcast (create Unit))

// wait requires Mutex.t which is not in scope here

// Invalid
(signal Num)
(broadcast Str)
(signal true)
