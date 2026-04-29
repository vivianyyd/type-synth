// 0-basics.types, 1-comparison.types, 4-arith.types, 7-str.types, 44-in-channel-mod.types

// Channel values
stdin

// Opening channels
(open_bin Str)
(open_text Str)

// Closing
(close stdin)
(close_noerr stdin)
(close (open_bin Str))
(close (open_text Str))

// input_char: t -> char option
(input_char stdin)
(input_char (open_bin Str))
(input_char (open_text Str))

// input_byte: t -> int option
(input_byte stdin)
(input_byte (open_bin Str))

// input_line: t -> string option
(input_line stdin)
(input_line (open_text Str))

// really_input_string: t -> int -> string option
(really_input_string stdin Num)
(really_input_string (open_bin Str) Num)

// input_all: t -> string
(input_all stdin)
(input_all (open_bin Str))

// input_lines: t -> string list
(input_lines stdin)
(input_lines (open_text Str))

// is_binary_mode, isatty: t -> bool
(is_binary_mode stdin)
(is_binary_mode (open_bin Str))
(isatty stdin)

// set_binary_mode: t -> bool -> unit
(set_binary_mode stdin true)
(set_binary_mode stdin false)
(set_binary_mode (open_bin Str) true)

// with_open_bin: string -> (t -> 'a) -> 'a
(with_open_bin Str input_all)
(with_open_bin Str input_lines)
(with_open_bin Str close)
(with_open_text Str input_all)

// Chaining: open_bin/open_text return t — use in all channel operations
(input_char (open_bin Str))
(input_line (open_text Str))
(input_all (open_bin Str))
(input_lines (open_text Str))
(is_binary_mode (open_bin Str))
(isatty (open_text Str))
(close (open_bin Str))

// input_all returns string
(= (input_all stdin) Str)
(^ (input_all stdin) Str)
(^ (input_all stdin) (input_all (open_text Str)))

// input_lines returns string list
(= (input_lines stdin) (cons Str []))
(length (input_lines stdin))
(hd (input_lines stdin))

// is_binary_mode / isatty return bool
(= (is_binary_mode stdin) true)
(= (isatty stdin) false)
(not (is_binary_mode stdin))
(not (isatty stdin))
(set_binary_mode stdin (is_binary_mode stdin))

// with_open_bin result inherits type of body function
(= (with_open_bin Str input_all) Str)
(^ (with_open_bin Str input_all) Str)
(= (with_open_bin Str is_binary_mode) true)

// input_char returns char option — can compare but not use directly as char
(= (input_char stdin) (input_char stdin))
(= (input_byte stdin) (input_byte stdin))
(= (input_line stdin) (input_line stdin))

// Invalid: wrong types used in channel ops
(input_char Num)
(input_all Str)
(close Num)
(set_binary_mode stdin Num)
(with_open_bin Num input_all)
(^ (input_char stdin) Str)
(succ (input_all stdin))
(not (input_all stdin))
