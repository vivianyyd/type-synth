// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 13_io.types, 17_out.types, 60_printexc_mod.types

// get_backtrace: unit -> string
(Printexc.get_backtrace Unit)

// backtrace_status: unit -> bool
(Printexc.backtrace_status Unit)

// record_backtrace: bool -> unit
(Printexc.record_backtrace true)
(Printexc.record_backtrace false)

// get_raw_backtrace: unit -> raw_backtrace
(Printexc.get_raw_backtrace Unit)

// get_callstack: int -> raw_backtrace
(Printexc.get_callstack Num)

// raw_backtrace_to_string: raw_backtrace -> string
(Printexc.raw_backtrace_to_string (Printexc.get_raw_backtrace Unit))
(Printexc.raw_backtrace_to_string (Printexc.get_callstack Num))

// raw_backtrace_length: raw_backtrace -> int
(Printexc.raw_backtrace_length (Printexc.get_raw_backtrace Unit))
(Printexc.raw_backtrace_length (Printexc.get_callstack Num))

// get_raw_backtrace_slot: raw_backtrace -> int -> raw_backtrace_slot
(Printexc.get_raw_backtrace_slot (Printexc.get_raw_backtrace Unit) Num)
(Printexc.get_raw_backtrace_slot (Printexc.get_callstack Num) Num)

// convert_raw_backtrace_slot: raw_backtrace_slot -> backtrace_slot
(Printexc.convert_raw_backtrace_slot (Printexc.get_raw_backtrace_slot (Printexc.get_raw_backtrace Unit) Num))

// get_backtrace_slot: raw_backtrace -> int -> backtrace_slot
(Printexc.get_backtrace_slot (Printexc.get_raw_backtrace Unit) Num)
(Printexc.get_backtrace_slot (Printexc.get_callstack Num) Num)

// print_raw_backtrace: out_channel -> raw_backtrace -> unit
(Printexc.print_raw_backtrace stdout (Printexc.get_raw_backtrace Unit))
(Printexc.print_raw_backtrace stdout (Printexc.get_callstack Num))
(Printexc.print_raw_backtrace stderr (Printexc.get_raw_backtrace Unit))

// Chaining: get_backtrace returns string — use in string ops
((=) (Printexc.get_backtrace Unit) Str)
((^) (Printexc.get_backtrace Unit) Str)
((^) Str (Printexc.get_backtrace Unit))
((^) (Printexc.get_backtrace Unit) (Printexc.get_backtrace Unit))
((=) (Printexc.get_backtrace Unit) (Printexc.raw_backtrace_to_string (Printexc.get_raw_backtrace Unit)))

// raw_backtrace_to_string returns string
((=) (Printexc.raw_backtrace_to_string (Printexc.get_raw_backtrace Unit)) Str)
((^) (Printexc.raw_backtrace_to_string (Printexc.get_raw_backtrace Unit)) Str)
((^) (Printexc.raw_backtrace_to_string (Printexc.get_raw_backtrace Unit)) (Printexc.raw_backtrace_to_string (Printexc.get_callstack Num)))

// raw_backtrace_length returns int
((=) (Printexc.raw_backtrace_length (Printexc.get_raw_backtrace Unit)) Num)
((<) (Printexc.raw_backtrace_length (Printexc.get_callstack Num)) Num)
(succ (Printexc.raw_backtrace_length (Printexc.get_raw_backtrace Unit)))
(Printexc.get_raw_backtrace_slot (Printexc.get_raw_backtrace Unit) (Printexc.raw_backtrace_length (Printexc.get_raw_backtrace Unit)))
(Printexc.get_callstack (Printexc.raw_backtrace_length (Printexc.get_raw_backtrace Unit)))

// get_callstack returns raw_backtrace — chain into raw_backtrace ops
(Printexc.raw_backtrace_to_string (Printexc.get_callstack Num))
(Printexc.raw_backtrace_length (Printexc.get_callstack Num))
(Printexc.print_raw_backtrace stdout (Printexc.get_callstack Num))
((=) (Printexc.raw_backtrace_length (Printexc.get_callstack Num)) Num)
(Printexc.get_raw_backtrace_slot (Printexc.get_callstack Num) (Printexc.raw_backtrace_length (Printexc.get_callstack Num)))

// backtrace_status returns bool
((=) (Printexc.backtrace_status Unit) true)
(not (Printexc.backtrace_status Unit))
(Printexc.record_backtrace (Printexc.backtrace_status Unit))
((&&) (Printexc.backtrace_status Unit) (Printexc.backtrace_status Unit))

// record_backtrace returns unit — chain into clear_parser-style sequencing
(Printexc.record_backtrace (Printexc.backtrace_status Unit))

// Invalid
(succ (Printexc.get_backtrace Unit))
(not (Printexc.get_backtrace Unit))
(succ (Printexc.backtrace_status Unit))
(Printexc.raw_backtrace_to_string Str)
(Printexc.raw_backtrace_length Num)
(Printexc.get_raw_backtrace_slot Num Num)
(Printexc.record_backtrace Num)
(Printexc.print_raw_backtrace Str (Printexc.get_raw_backtrace Unit))
(succ (Printexc.raw_backtrace_to_string (Printexc.get_raw_backtrace Unit)))
(not (Printexc.raw_backtrace_length (Printexc.get_raw_backtrace Unit)))
