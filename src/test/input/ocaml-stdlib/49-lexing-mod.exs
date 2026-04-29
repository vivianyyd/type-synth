// 0-basics.types, 1-comparison.types, 4-arith.types, 7-str.types, 13-io.types, 49-lexing-mod.types

// dummy_pos: position constant
dummy_pos

// Constructing lexbufs
(from_string Str)
(from_channel stdin)

// set_position, set_filename: lexbuf -> ... -> unit
(set_position (from_string Str) dummy_pos)
(set_filename (from_string Str) Str)

// with_positions: lexbuf -> bool
(with_positions (from_string Str))
(with_positions (from_channel stdin))

// lexeme: lexbuf -> string
(lexeme (from_string Str))
(lexeme (from_channel stdin))

// lexeme_char: lexbuf -> int -> char
(lexeme_char (from_string Str) Num)
(lexeme_char (from_channel stdin) Num)

// lexeme_start / lexeme_end: lexbuf -> int
(lexeme_start (from_string Str))
(lexeme_end (from_string Str))
(lexeme_start (from_channel stdin))
(lexeme_end (from_channel stdin))

// lexeme_start_p / lexeme_end_p: lexbuf -> position
(lexeme_start_p (from_string Str))
(lexeme_end_p (from_string Str))

// new_line, flush_input: lexbuf -> unit
(new_line (from_string Str))
(flush_input (from_string Str))

// Chaining: from_string/from_channel return lexbuf — pass to all lexbuf ops
(lexeme (from_string Str))
(lexeme_start (from_string Str))
(lexeme_end (from_string Str))
(with_positions (from_string Str))
(new_line (from_string Str))
(set_filename (from_string Str) Str)
(set_position (from_string Str) (lexeme_start_p (from_string Str)))
(set_position (from_string Str) dummy_pos)

// lexeme returns string — use in string ops
(= (lexeme (from_string Str)) Str)
(^ (lexeme (from_string Str)) Str)
(^ (lexeme (from_string Str)) (lexeme (from_channel stdin)))

// lexeme_start / lexeme_end return int — use in int ops
(= (lexeme_start (from_string Str)) Num)
(< (lexeme_start (from_string Str)) (lexeme_end (from_string Str)))
(succ (lexeme_start (from_string Str)))
(- (lexeme_end (from_string Str)) (lexeme_start (from_string Str)))
(lexeme_char (from_string Str) (lexeme_start (from_string Str)))
(lexeme_char (from_string Str) (lexeme_end (from_string Str)))

// lexeme_char returns char
(= (lexeme_char (from_string Str) Num) Char)

// with_positions returns bool
(= (with_positions (from_string Str)) true)
(not (with_positions (from_string Str)))

// lexeme_start_p / lexeme_end_p return position — can pass to set_position
(set_position (from_string Str) (lexeme_start_p (from_string Str)))
(set_position (from_string Str) (lexeme_end_p (from_string Str)))

// Invalid: wrong types in lexbuf operations
(lexeme Str)
(lexeme_start Num)
(set_filename (from_string Str) Num)
(lexeme_char (from_string Str) Str)
(^ (lexeme_start (from_string Str)) Str)
(not (lexeme_start (from_string Str)))
(succ (lexeme (from_string Str)))
(set_position Str dummy_pos)
