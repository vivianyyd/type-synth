// 0_basics.types, 1_comparison.types, 16_stdin.types

(read_line Unit)
(read_int_opt Unit)
(read_int Unit)
(read_float_opt Unit)
(read_float Unit)

((=) (read_int Unit) Num)
((=) (read_float Unit) Flt)
((=) (read_line Unit) Str)

(read_line Num)
(read_line Str)
(read_int Str)
(read_float Num)

// read_int returns int: use in int comparisons
((=) (read_int Unit) Num)
((<) (read_int Unit) Num)
((>) (read_int Unit) Num)
((=) (read_int Unit) (read_int Unit))
((<) (read_int Unit) (read_int Unit))

// read_float returns float: use in float comparisons
((=) (read_float Unit) Flt)
((=) (read_float Unit) (read_float Unit))

// read_line returns string: use in string comparisons
((=) (read_line Unit) Str)
((=) (read_line Unit) (read_line Unit))

// read_int_opt/read_float_opt return option types
((=) (read_int_opt Unit) (read_int_opt Unit))
((=) (read_float_opt Unit) (read_float_opt Unit))

// invalid: using output of one read as input to wrong-typed operation
(read_int (read_line Unit))
((=) (read_int Unit) (read_float Unit))
