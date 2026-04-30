// 0_basics.types, 1_comparison.types, 4_arith.types, 13_io.types, 17_out.types, 18_in.types, 25_buffer_mod.types

// Construction
(create Num)

// Inspection: length, contents, nth, sub
(length (create Num))
(contents (create Num))
(nth (create Num) Num)
(sub (create Num) Num Num)

// Mutation: add_char, add_string, add_substring
(add_char (create Num) Char)
(add_string (create Num) Str)
(add_substring (create Num) Str Num Num)
(add_uint8 (create Num) Num)
(add_int8 (create Num) Num)
(add_uint16_ne (create Num) Num)
(add_uint16_be (create Num) Num)
(add_uint16_le (create Num) Num)
(add_int16_ne (create Num) Num)
(add_int16_be (create Num) Num)
(add_int16_le (create Num) Num)

// add_buffer
(add_buffer (create Num) (create Num))

// Mutation: clear, reset, truncate
(clear (create Num))
(reset (create Num))
(truncate (create Num) Num)

// Output to channel
(output_buffer stdout (create Num))
(output_buffer stderr (create Num))

// add_channel
(add_channel (create Num) stdin Num)

// add_substitute: (string -> string) argument
(add_substitute (create Num) (fun s1 -> s1) Str)
(add_substitute (create Num) (fun s2 -> (^ s2 Str)) Str)

// Chaining: outputs of functions used as inputs
(= (length (create Num)) Num)
(= (contents (create Num)) Str)
(= (nth (create Num) Num) Char)
(= (sub (create Num) Num Num) Str)

// length returns int: use in arithmetic and comparisons
(succ (length (create Num)))
(< (length (create Num)) Num)
(= (length (create Num)) (length (create Num)))
(truncate (create Num) (length (create Num)))
(sub (create Num) Num (length (create Num)))
(nth (create Num) (length (create Num)))

// contents returns string: use in string operations
(^ (contents (create Num)) Str)
(^ Str (contents (create Num)))
(= (contents (create Num)) (contents (create Num)))
(add_string (create Num) (contents (create Num)))
(add_string (create Num) (sub (create Num) Num Num))

// nth returns char: use where char expected
(= (nth (create Num) Num) Char)
(add_char (create Num) (nth (create Num) Num))

// Invalid
(length Num)
(contents Num)
(nth (create Num) Str)
(add_char (create Num) Num)
(add_string (create Num) Num)
(truncate (create Num) Str)
