// 0_basics.types, 4_arith.types, 7_str.types, 58_out_channel_mod.types

// Channel constants
stdout
stderr

// open_bin, open_text: string -> t
(open_bin Str)
(open_text Str)

// close, close_noerr: t -> unit
(close stdout)
(close stderr)
(close (open_bin Str))
(close_noerr (open_text Str))

// output_char: t -> char -> unit
(output_char stdout Char)
(output_char stderr Char)
(output_char (open_bin Str) Char)

// output_byte: t -> int -> unit
(output_byte stdout Num)
(output_byte stderr Num)

// output_string: t -> string -> unit
(output_string stdout Str)
(output_string stderr Str)
(output_string (open_text Str) Str)

// output_bytes: t -> bytes -> unit
(output_bytes stdout (Bytes.make Num Char))
(output_bytes stderr (Bytes.make Num Char))

// flush: t -> unit
(flush stdout)
(flush stderr)
(flush (open_bin Str))

// flush_all: unit -> unit
(flush_all Unit)

// pos: t -> int64
(pos stdout)
(pos stderr)
(pos (open_bin Str))

// length: t -> int64
(length stdout)
(length stderr)

// is_binary_mode: t -> bool
(is_binary_mode stdout)
(is_binary_mode stderr)
(is_binary_mode (open_bin Str))
(is_binary_mode (open_text Str))

// set_binary_mode: t -> bool -> unit
(set_binary_mode stdout true)
(set_binary_mode stderr false)

// is_buffered: t -> bool
(is_buffered stdout)
(is_buffered (open_bin Str))

// set_buffered: t -> bool -> unit
(set_buffered stdout true)
(set_buffered stderr false)

// isatty: t -> bool
(isatty stdout)
(isatty stderr)
(isatty (open_bin Str))

// Chaining: open_bin/open_text return t — use in output ops
(output_string (open_bin Str) Str)
(output_char (open_text Str) Char)
(output_byte (open_bin Str) Num)
(flush (open_text Str))
(close (open_bin Str))
(pos (open_text Str))
(is_binary_mode (open_bin Str))
(isatty (open_bin Str))

// is_binary_mode returns bool — use in set_binary_mode or comparisons
(set_binary_mode stdout (is_binary_mode stdout))
(set_binary_mode stderr (is_binary_mode stderr))
(= (is_binary_mode stdout) true)
(not (is_binary_mode stdout))
(&& (is_binary_mode stdout) (is_buffered stdout))
(|| (isatty stdout) (isatty stderr))

// is_buffered returns bool
(set_buffered stdout (is_buffered stdout))
(= (is_buffered stdout) false)
(not (is_buffered stdout))

// isatty returns bool
(= (isatty stdout) true)
(not (isatty stdout))
(set_binary_mode stdout (isatty stdout))

// pos / length return int64 — compare with = or seek
(= (pos stdout) (pos stderr))
(= (length stdout) (length stderr))

// Invalid
(output_string stdout Num)
(output_char stdout Num)
(output_byte stdout Char)
(output_string Str Str)
(flush Num)
(pos Num)
(length Str)
(is_binary_mode Num)
(set_binary_mode stdout Num)
(succ (pos stdout))
(succ (length stdout))
(not (pos stdout))
