// 0_basics.types, 1_comparison.types, 2_boolean.types, 4_arith.types, 7_str.types, 8_char.types, 28_char_mod.types

// code: char -> int
(Char.code Char)

// chr: int -> char
(Char.chr Num)

// escaped: char -> string
(Char.escaped Char)

// compare: char -> char -> int
(Char.compare Char Char)

// equal: char -> char -> bool
(Char.equal Char Char)

// hash
(Char.hash Char)
(Char.seeded_hash Num Char)

// Ascii predicates: char -> bool
(Char.Ascii.is_valid Char)
(Char.Ascii.is_upper Char)
(Char.Ascii.is_lower Char)
(Char.Ascii.is_letter Char)
(Char.Ascii.is_alphanum Char)
(Char.Ascii.is_white Char)
(Char.Ascii.is_blank Char)
(Char.Ascii.is_graphic Char)
(Char.Ascii.is_print Char)
(Char.Ascii.is_control Char)
(Char.Ascii.is_digit Char)
(Char.Ascii.is_hex_digit Char)

// Ascii digit conversions
(Char.Ascii.digit_to_int Char)
(Char.Ascii.digit_of_int Num)
(Char.Ascii.hex_digit_to_int Char)
(Char.Ascii.lower_hex_digit_of_int Num)
(Char.Ascii.upper_hex_digit_of_int Num)

// Ascii case conversion: char -> char
(Char.Ascii.uppercase Char)
(Char.Ascii.lowercase Char)
(Char.uppercase_ascii Char)
(Char.lowercase_ascii Char)

// Ascii constants
Char.Ascii.min
Char.Ascii.max

// Chaining: code returns int
((=) (Char.code Char) Num)
((<) (Char.code Char) Num)
(succ (Char.code Char))
(pred (Char.code Char))
((+) (Char.code Char) Num)
(Char.code (Char.chr Num))
(Char.chr (succ (Char.code Char)))
(Char.chr (pred (Char.code Char)))
(Char.chr ((+) (Char.code Char) (Char.code Char)))
(Char.chr (Char.code (Char.chr Num)))

// code output used in Ascii functions that take int
(Char.Ascii.digit_of_int (Char.code Char))
(Char.Ascii.lower_hex_digit_of_int (Char.code Char))
(Char.Ascii.upper_hex_digit_of_int (Char.code Char))

// chr returns char: use in char functions
((=) (Char.chr Num) Char)
(Char.code (Char.chr Num))
(Char.escaped (Char.chr Num))
(Char.uppercase_ascii (Char.chr Num))
(Char.lowercase_ascii (Char.chr Num))
(Char.Ascii.is_upper (Char.chr Num))
(Char.Ascii.uppercase (Char.chr Num))
(Char.equal (Char.chr Num) Char)
(Char.compare (Char.chr Num) Char)
(Char.equal (Char.chr (Char.code Char)) Char)

// escaped returns string
((=) (Char.escaped Char) Str)
((^) (Char.escaped Char) Str)
((^) (Char.escaped Char) (Char.escaped Char))

// compare returns int
((=) (Char.compare Char Char) Num)
((<) (Char.compare Char Char) Num)
(succ (Char.compare Char Char))
(Char.compare (Char.compare Char Char) Num)

// equal returns bool
((=) (Char.equal Char Char) true)

// Ascii.digit_to_int / hex_digit_to_int return int
((=) (Char.Ascii.digit_to_int Char) Num)
(succ (Char.Ascii.digit_to_int Char))
(Char.chr (Char.Ascii.digit_to_int Char))
(Char.Ascii.digit_of_int (Char.Ascii.digit_to_int Char))
((=) (Char.Ascii.hex_digit_to_int Char) Num)
(Char.Ascii.lower_hex_digit_of_int (Char.Ascii.hex_digit_to_int Char))

// Ascii case: char -> char
(Char.equal (Char.Ascii.uppercase Char) Char)
(Char.code (Char.Ascii.uppercase Char))
(Char.Ascii.is_upper (Char.Ascii.uppercase Char))
(Char.Ascii.lowercase (Char.Ascii.uppercase Char))
(Char.uppercase_ascii (Char.lowercase_ascii Char))
(Char.lowercase_ascii (Char.uppercase_ascii Char))

// hash returns int
((=) (Char.hash Char) Num)
(succ (Char.hash Char))

// Invalid
(Char.code Num)
(Char.chr Char)
(Char.code Str)
(Char.equal Char Num)
(Char.compare Char Num)
(Char.Ascii.digit_to_int Num)
(Char.Ascii.digit_of_int Char)

// Results used at their types: predicates give bools, conversions give chars and ints
(not (Char.Ascii.is_valid Char))
((&&) true (Char.Ascii.is_valid Char))
(succ (Char.Ascii.is_valid Char))
(Char.Ascii.is_valid Num)
(Char.Ascii.is_valid Str)
(not (Char.Ascii.is_upper Char))
((&&) true (Char.Ascii.is_upper Char))
(succ (Char.Ascii.is_upper Char))
(Char.Ascii.is_upper Num)
(Char.Ascii.is_upper Str)
(not (Char.Ascii.is_lower Char))
((&&) true (Char.Ascii.is_lower Char))
(succ (Char.Ascii.is_lower Char))
(Char.Ascii.is_lower Num)
(Char.Ascii.is_lower Str)
(not (Char.Ascii.is_letter Char))
((&&) true (Char.Ascii.is_letter Char))
(succ (Char.Ascii.is_letter Char))
(Char.Ascii.is_letter Num)
(Char.Ascii.is_letter Str)
(not (Char.Ascii.is_alphanum Char))
((&&) true (Char.Ascii.is_alphanum Char))
(succ (Char.Ascii.is_alphanum Char))
(Char.Ascii.is_alphanum Num)
(Char.Ascii.is_alphanum Str)
(not (Char.Ascii.is_white Char))
((&&) true (Char.Ascii.is_white Char))
(succ (Char.Ascii.is_white Char))
(Char.Ascii.is_white Num)
(Char.Ascii.is_white Str)
(not (Char.Ascii.is_blank Char))
((&&) true (Char.Ascii.is_blank Char))
(succ (Char.Ascii.is_blank Char))
(Char.Ascii.is_blank Num)
(Char.Ascii.is_blank Str)
(not (Char.Ascii.is_graphic Char))
((&&) true (Char.Ascii.is_graphic Char))
(succ (Char.Ascii.is_graphic Char))
(Char.Ascii.is_graphic Num)
(Char.Ascii.is_graphic Str)
(not (Char.Ascii.is_print Char))
((&&) true (Char.Ascii.is_print Char))
(succ (Char.Ascii.is_print Char))
(Char.Ascii.is_print Num)
(Char.Ascii.is_print Str)
(not (Char.Ascii.is_control Char))
((&&) true (Char.Ascii.is_control Char))
(succ (Char.Ascii.is_control Char))
(Char.Ascii.is_control Num)
(Char.Ascii.is_control Str)
(not (Char.Ascii.is_digit Char))
((&&) true (Char.Ascii.is_digit Char))
(succ (Char.Ascii.is_digit Char))
(Char.Ascii.is_digit Num)
(Char.Ascii.is_digit Str)
(not (Char.Ascii.is_hex_digit Char))
((&&) true (Char.Ascii.is_hex_digit Char))
(succ (Char.Ascii.is_hex_digit Char))
(Char.Ascii.is_hex_digit Num)
(Char.Ascii.is_hex_digit Str)
(Char.code (Char.Ascii.digit_of_int Num))
(Char.Ascii.uppercase (Char.Ascii.digit_of_int Num))
(succ (Char.Ascii.digit_of_int Num))
(Char.Ascii.digit_of_int Char)
(Char.code (Char.Ascii.lower_hex_digit_of_int Num))
(Char.Ascii.uppercase (Char.Ascii.lower_hex_digit_of_int Num))
(succ (Char.Ascii.lower_hex_digit_of_int Num))
(Char.Ascii.lower_hex_digit_of_int Char)
(Char.code (Char.Ascii.upper_hex_digit_of_int Num))
(Char.Ascii.uppercase (Char.Ascii.upper_hex_digit_of_int Num))
(succ (Char.Ascii.upper_hex_digit_of_int Num))
(Char.Ascii.upper_hex_digit_of_int Char)
(Char.code (Char.Ascii.uppercase Char))
(Char.Ascii.is_upper (Char.Ascii.uppercase Char))
(succ (Char.Ascii.uppercase Char))
(Char.Ascii.uppercase Num)
(Char.code (Char.Ascii.lowercase Char))
(Char.Ascii.is_upper (Char.Ascii.lowercase Char))
(succ (Char.Ascii.lowercase Char))
(Char.Ascii.lowercase Num)
(Char.code Char.Ascii.min)
(Char.Ascii.is_upper Char.Ascii.min)
(Char.equal Char Char.Ascii.min)
(succ Char.Ascii.min)
(not Char.Ascii.min)
((^) Str Char.Ascii.min)
(Char.code Char.Ascii.max)
(Char.Ascii.is_upper Char.Ascii.max)
(Char.equal Char Char.Ascii.max)
(succ Char.Ascii.max)
(not Char.Ascii.max)
((^) Str Char.Ascii.max)
(succ (Char.seeded_hash Num Char))
((+) Num (Char.seeded_hash Num Char))
(not (Char.seeded_hash Num Char))
(Char.seeded_hash Num Num)
(Char.seeded_hash Char)
(succ (Char.hash Char))
(not (Char.hash Char))
