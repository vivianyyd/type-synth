// 0-basics.types, 1-comparison.types, 10-strconv.types

(string_of_bool true)
(string_of_bool false)
(bool_of_string_opt Str)
(bool_of_string Str)

(string_of_int Num)
(int_of_string_opt Str)
(int_of_string Str)

(string_of_float Flt)
(float_of_string_opt Str)
(float_of_string Str)

(int_of_string (string_of_int Num))
(float_of_string (string_of_float Flt))
(bool_of_string (string_of_bool true))

(= (string_of_bool true) Str)
(= (string_of_int Num) Str)
(= (string_of_float Flt) Str)

(string_of_bool Num)
(string_of_int Str)
(string_of_int true)
(bool_of_string Num)
(float_of_string Num)
(int_of_string Num)

// string_of_* returns string: feed into string-consuming converters
(int_of_string (string_of_int Num))
(float_of_string (string_of_float Flt))
(bool_of_string (string_of_bool true))
(bool_of_string (string_of_bool false))
(int_of_string_opt (string_of_int Num))
(float_of_string_opt (string_of_float Flt))
(bool_of_string_opt (string_of_bool true))
(= (string_of_int (int_of_string Str)) Str)
(= (string_of_float (float_of_string Str)) Str)

// *_of_string returns int/float/bool: feed into further conversions
(string_of_int (int_of_string Str))
(string_of_float (float_of_string Str))
(string_of_bool (bool_of_string Str))

// output of one conversion is the right type for another conversion
(= (int_of_string (string_of_int Num)) Num)
(= (float_of_string (string_of_float Flt)) Flt)
(= (bool_of_string (string_of_bool true)) true)
(= (int_of_string Str) (int_of_string Str))
(= (string_of_int Num) (string_of_int Num))

// invalid cross-type chaining
(int_of_string (string_of_bool true))
(float_of_string (string_of_int Num))
(bool_of_string (string_of_int Num))
(string_of_int (float_of_string Str))
(string_of_float (bool_of_string Str))
