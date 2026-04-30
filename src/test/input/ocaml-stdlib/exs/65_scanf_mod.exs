// 65_scanf_mod.types

// Scanf functions take format strings, which cannot be constructed
// in this expression language (no format string literals).
// Scanning channel operations use opaque format types.

// Scanning submodule channel constants and simple ops
Scanning.stdin

// open_in, open_in_bin: string -> Scanning.in_channel
(Scanning.open_in Str)
(Scanning.open_in_bin Str)

// from_string: string -> Scanning.in_channel
(Scanning.from_string Str)

// from_bytes: bytes -> Scanning.in_channel
(Scanning.from_bytes (Bytes.make Num Char))

// from_channel: in_channel -> Scanning.in_channel
(Scanning.from_channel stdin)

// close_in: Scanning.in_channel -> unit
(Scanning.close_in Scanning.stdin)
(Scanning.close_in (Scanning.open_in Str))
(Scanning.close_in (Scanning.from_string Str))

// end_of_input: Scanning.in_channel -> bool
(Scanning.end_of_input Scanning.stdin)
(Scanning.end_of_input (Scanning.open_in Str))
(Scanning.end_of_input (Scanning.from_string Str))

// beginning_of_input: Scanning.in_channel -> bool
(Scanning.beginning_of_input Scanning.stdin)
(Scanning.beginning_of_input (Scanning.from_string Str))

// name_of_input: Scanning.in_channel -> string
(Scanning.name_of_input Scanning.stdin)
(Scanning.name_of_input (Scanning.open_in Str))

// unescaped: string -> string
(unescaped Str)

// Chaining: from_string/open_in return Scanning.in_channel
(Scanning.end_of_input (Scanning.from_string Str))
(Scanning.beginning_of_input (Scanning.from_string Str))
(Scanning.name_of_input (Scanning.from_string Str))
(Scanning.close_in (Scanning.from_string Str))
(Scanning.end_of_input (Scanning.open_in_bin Str))
(Scanning.name_of_input (Scanning.open_in_bin Str))
(Scanning.end_of_input (Scanning.from_channel stdin))

// end_of_input / beginning_of_input return bool
(= (Scanning.end_of_input Scanning.stdin) true)
(not (Scanning.end_of_input Scanning.stdin))
(= (Scanning.beginning_of_input (Scanning.from_string Str)) true)
(not (Scanning.beginning_of_input Scanning.stdin))
(&& (Scanning.end_of_input (Scanning.from_string Str)) (Scanning.beginning_of_input (Scanning.from_string Str)))

// name_of_input returns string
(= (Scanning.name_of_input Scanning.stdin) Str)
(^ (Scanning.name_of_input Scanning.stdin) Str)
(Scanning.open_in (Scanning.name_of_input Scanning.stdin))

// unescaped returns string
(= (unescaped Str) Str)
(^ (unescaped Str) Str)
(unescaped (unescaped Str))

// Invalid
(Scanning.end_of_input Str)
(Scanning.end_of_input Num)
(Scanning.close_in Str)
(Scanning.name_of_input Str)
(succ (Scanning.end_of_input Scanning.stdin))
(not (Scanning.name_of_input Scanning.stdin))
(unescaped Num)
