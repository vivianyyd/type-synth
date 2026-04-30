// 0_basics.types, 1_comparison.types, 4_arith.types, 6_float.types, 63_random_mod.types

// init: int -> unit
(Random.init Num)

// self_init: unit -> unit
(Random.self_init Unit)

// bits: unit -> int
(Random.bits Unit)

// int: int -> int
(Random.int Num)

// full_int: int -> int
(Random.full_int Num)

// float: float -> float
(Random.float Flt)

// bool: unit -> bool
(Random.bool Unit)

// bits32: unit -> Int32.t
(Random.bits32 Unit)

// bits64: unit -> Int64.t
(Random.bits64 Unit)

// get_state: unit -> State.t
(Random.get_state Unit)

// set_state: State.t -> unit
(Random.set_state (Random.get_state Unit))

// split: unit -> State.t
(Random.split Unit)

// State submodule
(Random.State.make_self_init Unit)
(Random.State.copy (Random.get_state Unit))
(Random.State.bits (Random.get_state Unit))
(Random.State.int (Random.get_state Unit) Num)
(Random.State.full_int (Random.get_state Unit) Num)
(Random.State.float (Random.get_state Unit) Flt)
(Random.State.bool (Random.get_state Unit))
(Random.State.bits32 (Random.get_state Unit))
(Random.State.bits64 (Random.get_state Unit))
(Random.State.split (Random.get_state Unit))
(Random.State.to_binary_string (Random.get_state Unit))
(Random.State.of_binary_string Str)

// Chaining: bits/int/full_int return int
((=) (Random.bits Unit) Num)
(succ (Random.bits Unit))
((<) (Random.bits Unit) Num)
((+) (Random.bits Unit) (Random.bits Unit))
(Random.int (Random.bits Unit))
(Random.full_int (Random.bits Unit))
(Random.init (Random.bits Unit))
((=) (Random.int Num) Num)
(succ (Random.int Num))
((<) (Random.int Num) (Random.full_int Num))
((+) (Random.int Num) (Random.full_int Num))

// float returns float
((=) (Random.float Flt) Flt)
((+.) (Random.float Flt) Flt)
(( *. ) (Random.float Flt) (Random.float Flt))
(Random.float (Random.float Flt))

// bool returns bool
((=) (Random.bool Unit) true)
(not (Random.bool Unit))
((&&) (Random.bool Unit) (Random.bool Unit))

// State.bits/int/full_int return int
((=) (Random.State.bits (Random.get_state Unit)) Num)
(succ (Random.State.bits (Random.get_state Unit)))
((+) (Random.State.bits (Random.get_state Unit)) (Random.State.int (Random.get_state Unit) Num))
(Random.State.int (Random.get_state Unit) (Random.State.bits (Random.get_state Unit)))

// State.float returns float
((+.) (Random.State.float (Random.get_state Unit) Flt) Flt)
(Random.State.float (Random.get_state Unit) (Random.State.float (Random.get_state Unit) Flt))

// State.bool returns bool
(not (Random.State.bool (Random.get_state Unit)))
((&&) (Random.State.bool (Random.get_state Unit)) (Random.bool Unit))

// get_state/split/State.copy/State.make_self_init return State.t
(Random.State.bits (Random.get_state Unit))
(Random.State.bits (Random.split Unit))
(Random.State.bits (Random.State.copy (Random.get_state Unit)))
(Random.State.bits (Random.State.split (Random.get_state Unit)))
(Random.State.float (Random.State.copy (Random.get_state Unit)) Flt)
(Random.State.to_binary_string (Random.State.copy (Random.get_state Unit)))
(Random.State.of_binary_string (Random.State.to_binary_string (Random.get_state Unit)))
(Random.set_state (Random.State.copy (Random.get_state Unit)))
(Random.set_state (Random.split Unit))

// State.to_binary_string returns string
((=) (Random.State.to_binary_string (Random.get_state Unit)) Str)
((^) (Random.State.to_binary_string (Random.get_state Unit)) Str)
(Random.State.of_binary_string (Random.State.to_binary_string (Random.get_state Unit)))

// Invalid
(succ (Random.bool Unit))
(not (Random.bits Unit))
((+.) (Random.int Num) Flt)
(Random.init (Random.bool Unit))
(Random.float Num)
(Random.State.int Num Num)
(Random.State.bits Num)
