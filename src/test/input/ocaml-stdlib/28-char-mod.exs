// 0-basics.types, 1-comparison.types, 4-arith.types, 7-str.types, 28-char-mod.types

// code: char -> int
(code Char)

// chr: int -> char
(chr Num)

// escaped: char -> string
(escaped Char)

// compare: char -> char -> int
(compare Char Char)

// equal: char -> char -> bool
(equal Char Char)

// hash
(hash Char)
(seeded_hash Num Char)

// Ascii predicates: char -> bool
(Ascii.is_valid Char)
(Ascii.is_upper Char)
(Ascii.is_lower Char)
(Ascii.is_letter Char)
(Ascii.is_alphanum Char)
(Ascii.is_white Char)
(Ascii.is_blank Char)
(Ascii.is_graphic Char)
(Ascii.is_print Char)
(Ascii.is_control Char)
(Ascii.is_digit Char)
(Ascii.is_hex_digit Char)

// Ascii digit conversions
(Ascii.digit_to_int Char)
(Ascii.digit_of_int Num)
(Ascii.hex_digit_to_int Char)
(Ascii.lower_hex_digit_of_int Num)
(Ascii.upper_hex_digit_of_int Num)

// Ascii case conversion: char -> char
(Ascii.uppercase Char)
(Ascii.lowercase Char)
(uppercase_ascii Char)
(lowercase_ascii Char)

// Ascii constants
Ascii.min
Ascii.max

// Chaining: code returns int
(= (code Char) Num)
(< (code Char) Num)
(succ (code Char))
(pred (code Char))
(+ (code Char) Num)
(code (chr Num))
(chr (succ (code Char)))
(chr (pred (code Char)))
(chr (+ (code Char) (code Char)))
(chr (code (chr Num)))

// code output used in Ascii functions that take int
(Ascii.digit_of_int (code Char))
(Ascii.lower_hex_digit_of_int (code Char))
(Ascii.upper_hex_digit_of_int (code Char))

// chr returns char: use in char functions
(= (chr Num) Char)
(code (chr Num))
(escaped (chr Num))
(uppercase_ascii (chr Num))
(lowercase_ascii (chr Num))
(Ascii.is_upper (chr Num))
(Ascii.uppercase (chr Num))
(equal (chr Num) Char)
(compare (chr Num) Char)
(equal (chr (code Char)) Char)

// escaped returns string
(= (escaped Char) Str)
(^ (escaped Char) Str)
(^ (escaped Char) (escaped Char))

// compare returns int
(= (compare Char Char) Num)
(< (compare Char Char) Num)
(succ (compare Char Char))
(compare (compare Char Char) Num)

// equal returns bool
(= (equal Char Char) true)

// Ascii.digit_to_int / hex_digit_to_int return int
(= (Ascii.digit_to_int Char) Num)
(succ (Ascii.digit_to_int Char))
(chr (Ascii.digit_to_int Char))
(Ascii.digit_of_int (Ascii.digit_to_int Char))
(= (Ascii.hex_digit_to_int Char) Num)
(Ascii.lower_hex_digit_of_int (Ascii.hex_digit_to_int Char))

// Ascii case: char -> char
(equal (Ascii.uppercase Char) Char)
(code (Ascii.uppercase Char))
(Ascii.is_upper (Ascii.uppercase Char))
(Ascii.lowercase (Ascii.uppercase Char))
(uppercase_ascii (lowercase_ascii Char))
(lowercase_ascii (uppercase_ascii Char))

// hash returns int
(= (hash Char) Num)
(succ (hash Char))

// Invalid
(code Num)
(chr Char)
(code Str)
(equal Char Num)
(compare Char Num)
(Ascii.digit_to_int Num)
(Ascii.digit_of_int Char)
