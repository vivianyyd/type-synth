// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 13_io.types, 49_lexing_mod.types

// dummy_pos: position constant
Lexing.dummy_pos

// Constructing lexbufs
(Lexing.from_string Str)
(Lexing.from_channel stdin)

// set_position, set_filename: lexbuf -> ... -> unit
(Lexing.set_position (Lexing.from_string Str) Lexing.dummy_pos)
(Lexing.set_filename (Lexing.from_string Str) Str)

// with_positions: lexbuf -> bool
(Lexing.with_positions (Lexing.from_string Str))
(Lexing.with_positions (Lexing.from_channel stdin))

// lexeme: lexbuf -> string
(Lexing.lexeme (Lexing.from_string Str))
(Lexing.lexeme (Lexing.from_channel stdin))

// lexeme_char: lexbuf -> int -> char
(Lexing.lexeme_char (Lexing.from_string Str) Num)
(Lexing.lexeme_char (Lexing.from_channel stdin) Num)

// lexeme_start / lexeme_end: lexbuf -> int
(Lexing.lexeme_start (Lexing.from_string Str))
(Lexing.lexeme_end (Lexing.from_string Str))
(Lexing.lexeme_start (Lexing.from_channel stdin))
(Lexing.lexeme_end (Lexing.from_channel stdin))

// lexeme_start_p / lexeme_end_p: lexbuf -> position
(Lexing.lexeme_start_p (Lexing.from_string Str))
(Lexing.lexeme_end_p (Lexing.from_string Str))

// new_line, flush_input: lexbuf -> unit
(Lexing.new_line (Lexing.from_string Str))
(Lexing.flush_input (Lexing.from_string Str))

// Chaining: from_string/from_channel return lexbuf — pass to all lexbuf ops
(Lexing.lexeme (Lexing.from_string Str))
(Lexing.lexeme_start (Lexing.from_string Str))
(Lexing.lexeme_end (Lexing.from_string Str))
(Lexing.with_positions (Lexing.from_string Str))
(Lexing.new_line (Lexing.from_string Str))
(Lexing.set_filename (Lexing.from_string Str) Str)
(Lexing.set_position (Lexing.from_string Str) (Lexing.lexeme_start_p (Lexing.from_string Str)))
(Lexing.set_position (Lexing.from_string Str) Lexing.dummy_pos)

// lexeme returns string — use in string ops
((=) (Lexing.lexeme (Lexing.from_string Str)) Str)
((^) (Lexing.lexeme (Lexing.from_string Str)) Str)
((^) (Lexing.lexeme (Lexing.from_string Str)) (Lexing.lexeme (Lexing.from_channel stdin)))

// lexeme_start / lexeme_end return int — use in int ops
((=) (Lexing.lexeme_start (Lexing.from_string Str)) Num)
((<) (Lexing.lexeme_start (Lexing.from_string Str)) (Lexing.lexeme_end (Lexing.from_string Str)))
(succ (Lexing.lexeme_start (Lexing.from_string Str)))
((-) (Lexing.lexeme_end (Lexing.from_string Str)) (Lexing.lexeme_start (Lexing.from_string Str)))
(Lexing.lexeme_char (Lexing.from_string Str) (Lexing.lexeme_start (Lexing.from_string Str)))
(Lexing.lexeme_char (Lexing.from_string Str) (Lexing.lexeme_end (Lexing.from_string Str)))

// lexeme_char returns char
((=) (Lexing.lexeme_char (Lexing.from_string Str) Num) Char)

// with_positions returns bool
((=) (Lexing.with_positions (Lexing.from_string Str)) true)
(not (Lexing.with_positions (Lexing.from_string Str)))

// lexeme_start_p / lexeme_end_p return position — can pass to set_position
(Lexing.set_position (Lexing.from_string Str) (Lexing.lexeme_start_p (Lexing.from_string Str)))
(Lexing.set_position (Lexing.from_string Str) (Lexing.lexeme_end_p (Lexing.from_string Str)))

// Invalid: wrong types in lexbuf operations
(Lexing.lexeme Str)
(Lexing.lexeme_start Num)
(Lexing.set_filename (Lexing.from_string Str) Num)
(Lexing.lexeme_char (Lexing.from_string Str) Str)
((^) (Lexing.lexeme_start (Lexing.from_string Str)) Str)
(not (Lexing.lexeme_start (Lexing.from_string Str)))
(succ (Lexing.lexeme (Lexing.from_string Str)))
(Lexing.set_position Str Lexing.dummy_pos)
