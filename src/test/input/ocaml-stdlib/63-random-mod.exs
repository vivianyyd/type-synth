// 0-basics.types, 1-comparison.types, 4-arith.types, 6-float.types, 63-random-mod.types

// init: int -> unit
(init Num)

// self_init: unit -> unit
(self_init Unit)

// bits: unit -> int
(bits Unit)

// int: int -> int
(int Num)

// full_int: int -> int
(full_int Num)

// float: float -> float
(float Flt)

// bool: unit -> bool
(bool Unit)

// bits32: unit -> Int32.t
(bits32 Unit)

// bits64: unit -> Int64.t
(bits64 Unit)

// get_state: unit -> State.t
(get_state Unit)

// set_state: State.t -> unit
(set_state (get_state Unit))

// split: unit -> State.t
(split Unit)

// State submodule
(State.make_self_init Unit)
(State.copy (get_state Unit))
(State.bits (get_state Unit))
(State.int (get_state Unit) Num)
(State.full_int (get_state Unit) Num)
(State.float (get_state Unit) Flt)
(State.bool (get_state Unit))
(State.bits32 (get_state Unit))
(State.bits64 (get_state Unit))
(State.split (get_state Unit))
(State.to_binary_string (get_state Unit))
(State.of_binary_string Str)

// Chaining: bits/int/full_int return int
(= (bits Unit) Num)
(succ (bits Unit))
(< (bits Unit) Num)
(+ (bits Unit) (bits Unit))
(int (bits Unit))
(full_int (bits Unit))
(init (bits Unit))
(= (int Num) Num)
(succ (int Num))
(< (int Num) (full_int Num))
(+ (int Num) (full_int Num))

// float returns float
(= (float Flt) Flt)
(+. (float Flt) Flt)
(*. (float Flt) (float Flt))
(float (float Flt))

// bool returns bool
(= (bool Unit) true)
(not (bool Unit))
(&& (bool Unit) (bool Unit))

// State.bits/int/full_int return int
(= (State.bits (get_state Unit)) Num)
(succ (State.bits (get_state Unit)))
(+ (State.bits (get_state Unit)) (State.int (get_state Unit) Num))
(State.int (get_state Unit) (State.bits (get_state Unit)))

// State.float returns float
(+. (State.float (get_state Unit) Flt) Flt)
(State.float (get_state Unit) (State.float (get_state Unit) Flt))

// State.bool returns bool
(not (State.bool (get_state Unit)))
(&& (State.bool (get_state Unit)) (bool Unit))

// get_state/split/State.copy/State.make_self_init return State.t
(State.bits (get_state Unit))
(State.bits (split Unit))
(State.bits (State.copy (get_state Unit)))
(State.bits (State.split (get_state Unit)))
(State.float (State.copy (get_state Unit)) Flt)
(State.to_binary_string (State.copy (get_state Unit)))
(State.of_binary_string (State.to_binary_string (get_state Unit)))
(set_state (State.copy (get_state Unit)))
(set_state (split Unit))

// State.to_binary_string returns string
(= (State.to_binary_string (get_state Unit)) Str)
(^ (State.to_binary_string (get_state Unit)) Str)
(State.of_binary_string (State.to_binary_string (get_state Unit)))

// Invalid
(succ (bool Unit))
(not (bits Unit))
(+. (int Num) Flt)
(init (bool Unit))
(float Num)
(State.int Num Num)
(State.bits Num)
