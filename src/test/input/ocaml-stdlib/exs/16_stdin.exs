// 0_basics.types, 1_comparison.types, 2_boolean.types, 4_arith.types, 6_float.types, 7_str.types, 9_unit.types, 16_stdin.types, 57_option_mod.types

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

// ---- Parameters, results and their types, one by one

// Every function takes unit (last argument wrong)
(read_line Str)
(read_line true)
(read_line Flt)
(read_int Num)
(read_int true)
(read_int_opt Num)
(read_int_opt Str)
(read_float_opt Num)
(read_float_opt Flt)
(read_float Str)
(read_float true)

// Results: int, float and string where those are needed, and not elsewhere
(succ (read_int Unit))
(not (read_int Unit))
((^) Str (read_line Unit))
((^) Str (read_int Unit))
((^) Str (read_float Unit))
((=) Num (read_line Unit))
((=) Num (read_float Unit))
((=) Flt (read_int Unit))
((=) Flt (read_line Unit))
((=) Str (read_float Unit))
(not (read_line Unit))
(succ (read_line Unit))
(succ (read_float Unit))

// Results of the _opt functions are options of int and float
(Option.is_some (read_int_opt Unit))
(Option.is_none (read_float_opt Unit))
((=) Num (Option.get (read_int_opt Unit)))
((=) Flt (Option.get (read_float_opt Unit)))
((=) Num (Option.value (read_int_opt Unit) Num))
((=) Flt (Option.value (read_float_opt Unit) Flt))
((=) Str (Option.get (read_int_opt Unit)))
((=) Str (Option.get (read_float_opt Unit)))
((=) Flt (Option.get (read_int_opt Unit)))
((=) Num (Option.get (read_float_opt Unit)))
(Option.value (read_int_opt Unit) Str)
(Option.value (read_int_opt Unit) Flt)
(Option.value (read_float_opt Unit) Num)
(Option.value (read_float_opt Unit) Str)
(succ (Option.get (read_int_opt Unit)))
(succ (Option.get (read_float_opt Unit)))
(succ (read_int_opt Unit))
(not (read_float_opt Unit))
((=) (read_int_opt Unit) Num)
((=) (read_float_opt Unit) Flt)
((=) (read_int_opt Unit) (read_float_opt Unit))
