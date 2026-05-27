// 0_basics.types, 4_arith.types, 8_char.types

(int_of_char Char)
(char_of_int Num)

(char_of_int (int_of_char Char))
(int_of_char (char_of_int Num))

(int_of_char Num)
(char_of_int Char)
(int_of_char Str)
(char_of_int Str)

// int_of_char returns int: use in arithmetic and int comparisons
(succ (int_of_char Char))
(pred (int_of_char Char))
((+) (int_of_char Char) Num)
((-) (int_of_char Char) (int_of_char Char))

// char_of_int returns char: use in further char/int conversions
(int_of_char (char_of_int Num))
(int_of_char (char_of_int (succ Num)))
(int_of_char (char_of_int (int_of_char Char)))

// deeper chains
(char_of_int (succ (int_of_char Char)))
(char_of_int (pred (int_of_char Char)))
(char_of_int ((+) (int_of_char Char) (int_of_char Char)))

// invalid chaining
(char_of_int (char_of_int Num))
(int_of_char (int_of_char Char))
(succ (char_of_int Num))
