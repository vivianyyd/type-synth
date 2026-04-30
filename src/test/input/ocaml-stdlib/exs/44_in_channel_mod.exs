// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 44_in_channel_mod.types

// Channel values
In_channel.stdin

// Opening channels
(In_channel.open_bin Str)
(In_channel.open_text Str)

// Closing
(In_channel.close In_channel.stdin)
(In_channel.close_noerr In_channel.stdin)
(In_channel.close (In_channel.open_bin Str))
(In_channel.close (In_channel.open_text Str))

// input_char: t -> char option
(In_channel.input_char In_channel.stdin)
(In_channel.input_char (In_channel.open_bin Str))
(In_channel.input_char (In_channel.open_text Str))

// input_byte: t -> int option
(In_channel.input_byte In_channel.stdin)
(In_channel.input_byte (In_channel.open_bin Str))

// input_line: t -> string option
(In_channel.input_line In_channel.stdin)
(In_channel.input_line (In_channel.open_text Str))

// really_input_string: t -> int -> string option
(In_channel.really_input_string In_channel.stdin Num)
(In_channel.really_input_string (In_channel.open_bin Str) Num)

// input_all: t -> string
(In_channel.input_all In_channel.stdin)
(In_channel.input_all (In_channel.open_bin Str))

// input_lines: t -> string list
(In_channel.input_lines In_channel.stdin)
(In_channel.input_lines (In_channel.open_text Str))

// is_binary_mode, isatty: t -> bool
(In_channel.is_binary_mode In_channel.stdin)
(In_channel.is_binary_mode (In_channel.open_bin Str))
(In_channel.isatty In_channel.stdin)

// set_binary_mode: t -> bool -> unit
(In_channel.set_binary_mode In_channel.stdin true)
(In_channel.set_binary_mode In_channel.stdin false)
(In_channel.set_binary_mode (In_channel.open_bin Str) true)

// with_open_bin: string -> (t -> 'a) -> 'a
(In_channel.with_open_bin Str In_channel.input_all)
(In_channel.with_open_bin Str In_channel.input_lines)
(In_channel.with_open_bin Str In_channel.close)
(In_channel.with_open_text Str In_channel.input_all)

// Chaining: open_bin/open_text return t — use in all channel operations
(In_channel.input_char (In_channel.open_bin Str))
(In_channel.input_line (In_channel.open_text Str))
(In_channel.input_all (In_channel.open_bin Str))
(In_channel.input_lines (In_channel.open_text Str))
(In_channel.is_binary_mode (In_channel.open_bin Str))
(In_channel.isatty (In_channel.open_text Str))
(In_channel.close (In_channel.open_bin Str))

// input_all returns string
((=) (In_channel.input_all In_channel.stdin) Str)
((^) (In_channel.input_all In_channel.stdin) Str)
((^) (In_channel.input_all In_channel.stdin) (In_channel.input_all (In_channel.open_text Str)))

// input_lines returns string list
((=) (In_channel.input_lines In_channel.stdin) (cons Str []))
(In_channel.length (In_channel.input_lines In_channel.stdin))
(hd (In_channel.input_lines In_channel.stdin))

// is_binary_mode / isatty return bool
((=) (In_channel.is_binary_mode In_channel.stdin) true)
((=) (In_channel.isatty In_channel.stdin) false)
(not (In_channel.is_binary_mode In_channel.stdin))
(not (In_channel.isatty In_channel.stdin))
(In_channel.set_binary_mode In_channel.stdin (In_channel.is_binary_mode In_channel.stdin))

// with_open_bin result inherits type of body function
((=) (In_channel.with_open_bin Str In_channel.input_all) Str)
((^) (In_channel.with_open_bin Str In_channel.input_all) Str)
((=) (In_channel.with_open_bin Str In_channel.is_binary_mode) true)

// input_char returns char option — can compare but not use directly as char
((=) (In_channel.input_char In_channel.stdin) (In_channel.input_char In_channel.stdin))
((=) (In_channel.input_byte In_channel.stdin) (In_channel.input_byte In_channel.stdin))
((=) (In_channel.input_line In_channel.stdin) (In_channel.input_line In_channel.stdin))

// Invalid: wrong types used in channel ops
(In_channel.input_char Num)
(In_channel.input_all Str)
(In_channel.close Num)
(In_channel.set_binary_mode In_channel.stdin Num)
(In_channel.with_open_bin Num In_channel.input_all)
((^) (In_channel.input_char In_channel.stdin) Str)
(succ (In_channel.input_all In_channel.stdin))
(not (In_channel.input_all In_channel.stdin))
