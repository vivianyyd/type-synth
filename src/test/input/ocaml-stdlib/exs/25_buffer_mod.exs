// 0_basics.types, 1_comparison.types, 4_arith.types, 13_io.types, 17_out.types, 18_in.types, 25_buffer_mod.types

// Construction
(Buffer.create Num)

// Inspection: length, contents, nth, sub
(Buffer.length (Buffer.create Num))
(Buffer.contents (Buffer.create Num))
(Buffer.nth (Buffer.create Num) Num)
(Buffer.sub (Buffer.create Num) Num Num)

// Mutation: add_char, add_string, add_substring
(Buffer.add_char (Buffer.create Num) Char)
(Buffer.add_string (Buffer.create Num) Str)
(Buffer.add_substring (Buffer.create Num) Str Num Num)
(Buffer.add_uint8 (Buffer.create Num) Num)
(Buffer.add_int8 (Buffer.create Num) Num)
(Buffer.add_uint16_ne (Buffer.create Num) Num)
(Buffer.add_uint16_be (Buffer.create Num) Num)
(Buffer.add_uint16_le (Buffer.create Num) Num)
(Buffer.add_int16_ne (Buffer.create Num) Num)
(Buffer.add_int16_be (Buffer.create Num) Num)
(Buffer.add_int16_le (Buffer.create Num) Num)

// add_buffer
(Buffer.add_buffer (Buffer.create Num) (Buffer.create Num))

// Mutation: clear, reset, truncate
(Buffer.clear (Buffer.create Num))
(Buffer.reset (Buffer.create Num))
(Buffer.truncate (Buffer.create Num) Num)

// Output to channel
(Buffer.output_buffer stdout (Buffer.create Num))
(Buffer.output_buffer stderr (Buffer.create Num))

// add_channel
(Buffer.add_channel (Buffer.create Num) stdin Num)

// add_substitute: (string -> string) argument
(Buffer.add_substitute (Buffer.create Num) (fun s1 -> s1) Str)
(Buffer.add_substitute (Buffer.create Num) (fun s2 -> ((^) s2 Str)) Str)

// Chaining: outputs of functions used as inputs
((=) (Buffer.length (Buffer.create Num)) Num)
((=) (Buffer.contents (Buffer.create Num)) Str)
((=) (Buffer.nth (Buffer.create Num) Num) Char)
((=) (Buffer.sub (Buffer.create Num) Num Num) Str)

// length returns int: use in arithmetic and comparisons
(succ (Buffer.length (Buffer.create Num)))
((<) (Buffer.length (Buffer.create Num)) Num)
((=) (Buffer.length (Buffer.create Num)) (Buffer.length (Buffer.create Num)))
(Buffer.truncate (Buffer.create Num) (Buffer.length (Buffer.create Num)))
(Buffer.sub (Buffer.create Num) Num (Buffer.length (Buffer.create Num)))
(Buffer.nth (Buffer.create Num) (Buffer.length (Buffer.create Num)))

// contents returns string: use in string operations
((^) (Buffer.contents (Buffer.create Num)) Str)
((^) Str (Buffer.contents (Buffer.create Num)))
((=) (Buffer.contents (Buffer.create Num)) (Buffer.contents (Buffer.create Num)))
(Buffer.add_string (Buffer.create Num) (Buffer.contents (Buffer.create Num)))
(Buffer.add_string (Buffer.create Num) (Buffer.sub (Buffer.create Num) Num Num))

// nth returns char: use where char expected
((=) (Buffer.nth (Buffer.create Num) Num) Char)
(Buffer.add_char (Buffer.create Num) (Buffer.nth (Buffer.create Num) Num))

// Invalid
(Buffer.length Num)
(Buffer.contents Num)
(Buffer.nth (Buffer.create Num) Str)
(Buffer.add_char (Buffer.create Num) Num)
(Buffer.add_string (Buffer.create Num) Num)
(Buffer.truncate (Buffer.create Num) Str)
