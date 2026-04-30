// 0_basics.types, 14_stdout.types

(print_char Char)
(print_string Str)
(print_int Num)
(print_float Flt)
(print_endline Str)
(print_newline Unit)

(print_char Num)
(print_string Num)
(print_int Str)
(print_float Num)
(print_endline Num)
(print_newline Str)
(print_newline Num)

// print_* functions return unit: output can be passed to print_newline (unit -> unit)
(print_newline (print_newline Unit))
(print_newline (print_string Str))
(print_newline (print_int Num))
(print_newline (print_char Char))
(print_newline (print_float Flt))
(print_newline (print_endline Str))

// invalid: passing unit result of one print to a print that expects a typed argument
(print_int (print_int Num))
(print_string (print_string Str))
(print_char (print_char Char))
