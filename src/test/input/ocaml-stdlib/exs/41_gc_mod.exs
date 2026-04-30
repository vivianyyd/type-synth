// 0_basics.types, 1_comparison.types, 4_arith.types, 6_float.types, 9_unit.types, 14_stdout.types, 17_out.types, 41_gc_mod.types

// Unit-returning GC operations
(Gc.minor Unit)
(Gc.major Unit)
(Gc.full_major Unit)
(Gc.compact Unit)
(Gc.finalise_release Unit)

// major_slice: int -> int
(Gc.major_slice Num)
(Gc.major_slice (succ Num))

// Float-returning queries
(Gc.minor_words Unit)
(Gc.allocated_bytes Unit)

// Int-returning queries
(Gc.get_minor_free Unit)

// finalise: ('a -> unit) -> 'a -> unit — first arg must be 'a -> unit
(Gc.finalise ignore Num)
(Gc.finalise ignore Str)
(Gc.finalise ignore true)
(Gc.finalise print_int Num)
(Gc.finalise print_string Str)

// finalise_last: (unit -> unit) -> 'a -> unit — first arg is unit -> unit
(Gc.finalise_last print_newline Num)
(Gc.finalise_last print_newline Str)
(Gc.finalise_last flush_all Num)

// create_alarm: (unit -> unit) -> alarm
(Gc.create_alarm print_newline)
(Gc.create_alarm flush_all)

// delete_alarm: alarm -> unit
(Gc.delete_alarm (Gc.create_alarm print_newline))
(Gc.delete_alarm (Gc.create_alarm flush_all))

// print_stat: out_channel -> unit
(Gc.print_stat stdout)
(Gc.print_stat stderr)

// Chaining: major_slice returns int
((=) (Gc.major_slice Num) Num)
(succ (Gc.major_slice Num))
((<) (Gc.major_slice Num) Num)
(Gc.major_slice (Gc.major_slice Num))
(Gc.major_slice (Gc.get_minor_free Unit))
((+) (Gc.major_slice Num) (Gc.get_minor_free Unit))

// get_minor_free returns int
((=) (Gc.get_minor_free Unit) Num)
(succ (Gc.get_minor_free Unit))
((<) (Gc.get_minor_free Unit) Num)
(Gc.major_slice (Gc.get_minor_free Unit))

// minor_words / allocated_bytes return float
((=) (Gc.minor_words Unit) Flt)
((=) (Gc.allocated_bytes Unit) Flt)
((+.) (Gc.minor_words Unit) (Gc.allocated_bytes Unit))
((+.) (Gc.minor_words Unit) Flt)
((<) (Gc.minor_words Unit) (Gc.allocated_bytes Unit))

// create_alarm output is alarm — can only be passed to delete_alarm
(Gc.delete_alarm (Gc.create_alarm print_newline))
(Gc.delete_alarm (Gc.create_alarm flush_all))

// Invalid: wrong output types used in wrong contexts
(succ (Gc.minor_words Unit))
((+.) (Gc.major_slice Num) Flt)
(Gc.major_slice Flt)
(Gc.delete_alarm Num)
(Gc.delete_alarm Str)
(Gc.finalise succ Num)
(Gc.finalise_last print_int Num)
(succ (Gc.allocated_bytes Unit))
(not (Gc.get_minor_free Unit))
