// 65_scanf_mod.types

// Scanf functions take format strings, which cannot be constructed
// in this expression language (no format string literals).
// Scanning channel operations use opaque format types.

// Scanning submodule channel constants and simple ops
Scanf.Scanning.stdin

// open_in, open_in_bin: string -> Scanning.in_channel
(Scanf.Scanning.open_in Str)
(Scanf.Scanning.open_in_bin Str)

// from_string: string -> Scanning.in_channel
(Scanf.Scanning.from_string Str)

// from_bytes: bytes -> Scanning.in_channel
(Scanf.Scanning.from_bytes (Bytes.make Num Char))

// from_channel: in_channel -> Scanning.in_channel
(Scanf.Scanning.from_channel stdin)

// close_in: Scanning.in_channel -> unit
(Scanf.Scanning.close_in Scanf.Scanning.stdin)
(Scanf.Scanning.close_in (Scanf.Scanning.open_in Str))
(Scanf.Scanning.close_in (Scanf.Scanning.from_string Str))

// end_of_input: Scanning.in_channel -> bool
(Scanf.Scanning.end_of_input Scanf.Scanning.stdin)
(Scanf.Scanning.end_of_input (Scanf.Scanning.open_in Str))
(Scanf.Scanning.end_of_input (Scanf.Scanning.from_string Str))

// beginning_of_input: Scanning.in_channel -> bool
(Scanf.Scanning.beginning_of_input Scanf.Scanning.stdin)
(Scanf.Scanning.beginning_of_input (Scanf.Scanning.from_string Str))

// name_of_input: Scanning.in_channel -> string
(Scanf.Scanning.name_of_input Scanf.Scanning.stdin)
(Scanf.Scanning.name_of_input (Scanf.Scanning.open_in Str))

// unescaped: string -> string
(Scanf.unescaped Str)

// Chaining: from_string/open_in return Scanning.in_channel
(Scanf.Scanning.end_of_input (Scanf.Scanning.from_string Str))
(Scanf.Scanning.beginning_of_input (Scanf.Scanning.from_string Str))
(Scanf.Scanning.name_of_input (Scanf.Scanning.from_string Str))
(Scanf.Scanning.close_in (Scanf.Scanning.from_string Str))
(Scanf.Scanning.end_of_input (Scanf.Scanning.open_in_bin Str))
(Scanf.Scanning.name_of_input (Scanf.Scanning.open_in_bin Str))
(Scanf.Scanning.end_of_input (Scanf.Scanning.from_channel stdin))

// end_of_input / beginning_of_input return bool
((=) (Scanf.Scanning.end_of_input Scanf.Scanning.stdin) true)
(not (Scanf.Scanning.end_of_input Scanf.Scanning.stdin))
((=) (Scanf.Scanning.beginning_of_input (Scanf.Scanning.from_string Str)) true)
(not (Scanf.Scanning.beginning_of_input Scanf.Scanning.stdin))
((&&) (Scanf.Scanning.end_of_input (Scanf.Scanning.from_string Str)) (Scanf.Scanning.beginning_of_input (Scanf.Scanning.from_string Str)))

// name_of_input returns string
((=) (Scanf.Scanning.name_of_input Scanf.Scanning.stdin) Str)
((^) (Scanf.Scanning.name_of_input Scanf.Scanning.stdin) Str)
(Scanf.Scanning.open_in (Scanf.Scanning.name_of_input Scanf.Scanning.stdin))

// unescaped returns string
((=) (Scanf.unescaped Str) Str)
((^) (Scanf.unescaped Str) Str)
(Scanf.unescaped (Scanf.unescaped Str))

// Invalid
(Scanf.Scanning.end_of_input Str)
(Scanf.Scanning.end_of_input Num)
(Scanf.Scanning.close_in Str)
(Scanf.Scanning.name_of_input Str)
(succ (Scanf.Scanning.end_of_input Scanf.Scanning.stdin))
(not (Scanf.Scanning.name_of_input Scanf.Scanning.stdin))
(Scanf.unescaped Num)
