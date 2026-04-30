// 0_basics.types, 4_arith.types, 7_str.types, 58_out_channel_mod.types

// Channel constants
Out_channel.stdout
Out_channel.stderr

// open_bin, open_text: string -> t
(Out_channel.open_bin Str)
(Out_channel.open_text Str)

// close, close_noerr: t -> unit
(Out_channel.close Out_channel.stdout)
(Out_channel.close Out_channel.stderr)
(Out_channel.close (Out_channel.open_bin Str))
(Out_channel.close_noerr (Out_channel.open_text Str))

// output_char: t -> char -> unit
(Out_channel.output_char Out_channel.stdout Char)
(Out_channel.output_char Out_channel.stderr Char)
(Out_channel.output_char (Out_channel.open_bin Str) Char)

// output_byte: t -> int -> unit
(Out_channel.output_byte Out_channel.stdout Num)
(Out_channel.output_byte Out_channel.stderr Num)

// output_string: t -> string -> unit
(Out_channel.output_string Out_channel.stdout Str)
(Out_channel.output_string Out_channel.stderr Str)
(Out_channel.output_string (Out_channel.open_text Str) Str)

// output_bytes: t -> bytes -> unit
(Out_channel.output_bytes Out_channel.stdout (Bytes.make Num Char))
(Out_channel.output_bytes Out_channel.stderr (Bytes.make Num Char))

// flush: t -> unit
(Out_channel.flush Out_channel.stdout)
(Out_channel.flush Out_channel.stderr)
(Out_channel.flush (Out_channel.open_bin Str))

// flush_all: unit -> unit
(Out_channel.flush_all Unit)

// pos: t -> int64
(Out_channel.pos Out_channel.stdout)
(Out_channel.pos Out_channel.stderr)
(Out_channel.pos (Out_channel.open_bin Str))

// length: t -> int64
(Out_channel.length Out_channel.stdout)
(Out_channel.length Out_channel.stderr)

// is_binary_mode: t -> bool
(Out_channel.is_binary_mode Out_channel.stdout)
(Out_channel.is_binary_mode Out_channel.stderr)
(Out_channel.is_binary_mode (Out_channel.open_bin Str))
(Out_channel.is_binary_mode (Out_channel.open_text Str))

// set_binary_mode: t -> bool -> unit
(Out_channel.set_binary_mode Out_channel.stdout true)
(Out_channel.set_binary_mode Out_channel.stderr false)

// is_buffered: t -> bool
(Out_channel.is_buffered Out_channel.stdout)
(Out_channel.is_buffered (Out_channel.open_bin Str))

// set_buffered: t -> bool -> unit
(Out_channel.set_buffered Out_channel.stdout true)
(Out_channel.set_buffered Out_channel.stderr false)

// isatty: t -> bool
(Out_channel.isatty Out_channel.stdout)
(Out_channel.isatty Out_channel.stderr)
(Out_channel.isatty (Out_channel.open_bin Str))

// Chaining: open_bin/open_text return t — use in output ops
(Out_channel.output_string (Out_channel.open_bin Str) Str)
(Out_channel.output_char (Out_channel.open_text Str) Char)
(Out_channel.output_byte (Out_channel.open_bin Str) Num)
(Out_channel.flush (Out_channel.open_text Str))
(Out_channel.close (Out_channel.open_bin Str))
(Out_channel.pos (Out_channel.open_text Str))
(Out_channel.is_binary_mode (Out_channel.open_bin Str))
(Out_channel.isatty (Out_channel.open_bin Str))

// is_binary_mode returns bool — use in set_binary_mode or comparisons
(Out_channel.set_binary_mode Out_channel.stdout (Out_channel.is_binary_mode Out_channel.stdout))
(Out_channel.set_binary_mode Out_channel.stderr (Out_channel.is_binary_mode Out_channel.stderr))
((=) (Out_channel.is_binary_mode Out_channel.stdout) true)
(not (Out_channel.is_binary_mode Out_channel.stdout))
((&&) (Out_channel.is_binary_mode Out_channel.stdout) (Out_channel.is_buffered Out_channel.stdout))
((||) (Out_channel.isatty Out_channel.stdout) (Out_channel.isatty Out_channel.stderr))

// is_buffered returns bool
(Out_channel.set_buffered Out_channel.stdout (Out_channel.is_buffered Out_channel.stdout))
((=) (Out_channel.is_buffered Out_channel.stdout) false)
(not (Out_channel.is_buffered Out_channel.stdout))

// isatty returns bool
((=) (Out_channel.isatty Out_channel.stdout) true)
(not (Out_channel.isatty Out_channel.stdout))
(Out_channel.set_binary_mode Out_channel.stdout (Out_channel.isatty Out_channel.stdout))

// pos / length return int64 — compare with = or seek
((=) (Out_channel.pos Out_channel.stdout) (Out_channel.pos Out_channel.stderr))
((=) (Out_channel.length Out_channel.stdout) (Out_channel.length Out_channel.stderr))

// Invalid
(Out_channel.output_string Out_channel.stdout Num)
(Out_channel.output_char Out_channel.stdout Num)
(Out_channel.output_byte Out_channel.stdout Char)
(Out_channel.output_string Str Str)
(Out_channel.flush Num)
(Out_channel.pos Num)
(Out_channel.length Str)
(Out_channel.is_binary_mode Num)
(Out_channel.set_binary_mode Out_channel.stdout Num)
(succ (Out_channel.pos Out_channel.stdout))
(succ (Out_channel.length Out_channel.stdout))
(not (Out_channel.pos Out_channel.stdout))
