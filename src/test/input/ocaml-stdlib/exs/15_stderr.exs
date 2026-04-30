// 0_basics.types, 15_stderr.types

(prerr_char Char)
(prerr_string Str)
(prerr_int Num)
(prerr_float Flt)
(prerr_endline Str)
(prerr_newline Unit)

(prerr_char Num)
(prerr_string Num)
(prerr_int Str)
(prerr_float Num)
(prerr_endline Num)
(prerr_newline Str)
(prerr_newline Num)

// prerr_* functions return unit: output can be passed to prerr_newline (unit -> unit)
(prerr_newline (prerr_newline Unit))
(prerr_newline (prerr_string Str))
(prerr_newline (prerr_int Num))
(prerr_newline (prerr_char Char))
(prerr_newline (prerr_float Flt))
(prerr_newline (prerr_endline Str))

// invalid: passing unit result to a prerr expecting typed argument
(prerr_int (prerr_int Num))
(prerr_string (prerr_string Str))
(prerr_char (prerr_char Char))
