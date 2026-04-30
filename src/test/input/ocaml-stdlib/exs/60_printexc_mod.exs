// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 13_io.types, 17_out.types, 60_printexc_mod.types

// get_backtrace: unit -> string
(get_backtrace Unit)

// backtrace_status: unit -> bool
(backtrace_status Unit)

// record_backtrace: bool -> unit
(record_backtrace true)
(record_backtrace false)

// get_raw_backtrace: unit -> raw_backtrace
(get_raw_backtrace Unit)

// get_callstack: int -> raw_backtrace
(get_callstack Num)

// raw_backtrace_to_string: raw_backtrace -> string
(raw_backtrace_to_string (get_raw_backtrace Unit))
(raw_backtrace_to_string (get_callstack Num))

// raw_backtrace_length: raw_backtrace -> int
(raw_backtrace_length (get_raw_backtrace Unit))
(raw_backtrace_length (get_callstack Num))

// get_raw_backtrace_slot: raw_backtrace -> int -> raw_backtrace_slot
(get_raw_backtrace_slot (get_raw_backtrace Unit) Num)
(get_raw_backtrace_slot (get_callstack Num) Num)

// convert_raw_backtrace_slot: raw_backtrace_slot -> backtrace_slot
(convert_raw_backtrace_slot (get_raw_backtrace_slot (get_raw_backtrace Unit) Num))

// get_backtrace_slot: raw_backtrace -> int -> backtrace_slot
(get_backtrace_slot (get_raw_backtrace Unit) Num)
(get_backtrace_slot (get_callstack Num) Num)

// print_raw_backtrace: out_channel -> raw_backtrace -> unit
(print_raw_backtrace stdout (get_raw_backtrace Unit))
(print_raw_backtrace stdout (get_callstack Num))
(print_raw_backtrace stderr (get_raw_backtrace Unit))

// Chaining: get_backtrace returns string — use in string ops
(= (get_backtrace Unit) Str)
(^ (get_backtrace Unit) Str)
(^ Str (get_backtrace Unit))
(^ (get_backtrace Unit) (get_backtrace Unit))
(= (get_backtrace Unit) (raw_backtrace_to_string (get_raw_backtrace Unit)))

// raw_backtrace_to_string returns string
(= (raw_backtrace_to_string (get_raw_backtrace Unit)) Str)
(^ (raw_backtrace_to_string (get_raw_backtrace Unit)) Str)
(^ (raw_backtrace_to_string (get_raw_backtrace Unit)) (raw_backtrace_to_string (get_callstack Num)))

// raw_backtrace_length returns int
(= (raw_backtrace_length (get_raw_backtrace Unit)) Num)
(< (raw_backtrace_length (get_callstack Num)) Num)
(succ (raw_backtrace_length (get_raw_backtrace Unit)))
(get_raw_backtrace_slot (get_raw_backtrace Unit) (raw_backtrace_length (get_raw_backtrace Unit)))
(get_callstack (raw_backtrace_length (get_raw_backtrace Unit)))

// get_callstack returns raw_backtrace — chain into raw_backtrace ops
(raw_backtrace_to_string (get_callstack Num))
(raw_backtrace_length (get_callstack Num))
(print_raw_backtrace stdout (get_callstack Num))
(= (raw_backtrace_length (get_callstack Num)) Num)
(get_raw_backtrace_slot (get_callstack Num) (raw_backtrace_length (get_callstack Num)))

// backtrace_status returns bool
(= (backtrace_status Unit) true)
(not (backtrace_status Unit))
(record_backtrace (backtrace_status Unit))
(&& (backtrace_status Unit) (backtrace_status Unit))

// record_backtrace returns unit — chain into clear_parser-style sequencing
(record_backtrace (backtrace_status Unit))

// Invalid
(succ (get_backtrace Unit))
(not (get_backtrace Unit))
(succ (backtrace_status Unit))
(raw_backtrace_to_string Str)
(raw_backtrace_length Num)
(get_raw_backtrace_slot Num Num)
(record_backtrace Num)
(print_raw_backtrace Str (get_raw_backtrace Unit))
(succ (raw_backtrace_to_string (get_raw_backtrace Unit)))
(not (raw_backtrace_length (get_raw_backtrace Unit)))
