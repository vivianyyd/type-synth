// 0_basics.types, 1_comparison.types, 4_arith.types, 6_float.types, 9_unit.types, 14_stdout.types, 17_out.types, 41_gc_mod.types

// Unit-returning GC operations
(minor Unit)
(major Unit)
(full_major Unit)
(compact Unit)
(finalise_release Unit)

// major_slice: int -> int
(major_slice Num)
(major_slice (succ Num))

// Float-returning queries
(minor_words Unit)
(allocated_bytes Unit)

// Int-returning queries
(get_minor_free Unit)

// finalise: ('a -> unit) -> 'a -> unit — first arg must be 'a -> unit
(finalise ignore Num)
(finalise ignore Str)
(finalise ignore true)
(finalise print_int Num)
(finalise print_string Str)

// finalise_last: (unit -> unit) -> 'a -> unit — first arg is unit -> unit
(finalise_last print_newline Num)
(finalise_last print_newline Str)
(finalise_last flush_all Num)

// create_alarm: (unit -> unit) -> alarm
(create_alarm print_newline)
(create_alarm flush_all)

// delete_alarm: alarm -> unit
(delete_alarm (create_alarm print_newline))
(delete_alarm (create_alarm flush_all))

// print_stat: out_channel -> unit
(print_stat stdout)
(print_stat stderr)

// Chaining: major_slice returns int
(= (major_slice Num) Num)
(succ (major_slice Num))
(< (major_slice Num) Num)
(major_slice (major_slice Num))
(major_slice (get_minor_free Unit))
(+ (major_slice Num) (get_minor_free Unit))

// get_minor_free returns int
(= (get_minor_free Unit) Num)
(succ (get_minor_free Unit))
(< (get_minor_free Unit) Num)
(major_slice (get_minor_free Unit))

// minor_words / allocated_bytes return float
(= (minor_words Unit) Flt)
(= (allocated_bytes Unit) Flt)
(+. (minor_words Unit) (allocated_bytes Unit))
(+. (minor_words Unit) Flt)
(< (minor_words Unit) (allocated_bytes Unit))

// create_alarm output is alarm — can only be passed to delete_alarm
(delete_alarm (create_alarm print_newline))
(delete_alarm (create_alarm flush_all))

// Invalid: wrong output types used in wrong contexts
(succ (minor_words Unit))
(+. (major_slice Num) Flt)
(major_slice Flt)
(delete_alarm Num)
(delete_alarm Str)
(finalise succ Num)
(finalise_last print_int Num)
(succ (allocated_bytes Unit))
(not (get_minor_free Unit))
