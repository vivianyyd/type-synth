// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 8_char.types, 26_bytes_mod.types

// Construction
(Bytes.create Num)
(Bytes.make Num Char)
(Bytes.init Num (fun i1 -> char_of_int i1))
(Bytes.of_string Str)
(Bytes.copy (Bytes.create Num))
Bytes.empty

// Inspection
(Bytes.length (Bytes.create Num))
(Bytes.length (Bytes.make Num Char))
(Bytes.length Bytes.empty)
(Bytes.get (Bytes.make Num Char) Num)

// Conversion
(Bytes.to_string (Bytes.create Num))
(Bytes.to_string (Bytes.make Num Char))
(Bytes.to_string (Bytes.of_string Str))
(Bytes.unsafe_to_string (Bytes.create Num))
(Bytes.unsafe_of_string Str)

// Structural operations
(Bytes.copy (Bytes.make Num Char))
(Bytes.copy (Bytes.of_string Str))
(Bytes.sub (Bytes.make Num Char) Num Num)
(Bytes.sub_string (Bytes.make Num Char) Num Num)
(Bytes.cat (Bytes.create Num) (Bytes.create Num))
(Bytes.cat (Bytes.make Num Char) (Bytes.make Num Char))
(Bytes.concat Bytes.empty (cons (Bytes.make Num Char) []))
(Bytes.extend (Bytes.create Num) Num Num)
(Bytes.trim (Bytes.make Num Char))
(Bytes.escaped (Bytes.make Num Char))
(Bytes.uppercase_ascii (Bytes.make Num Char))
(Bytes.lowercase_ascii (Bytes.make Num Char))
(Bytes.capitalize_ascii (Bytes.make Num Char))
(Bytes.uncapitalize_ascii (Bytes.make Num Char))

// Searching
(Bytes.index (Bytes.make Num Char) Char)
(Bytes.index_opt (Bytes.make Num Char) Char)
(Bytes.rindex (Bytes.make Num Char) Char)
(Bytes.rindex_opt (Bytes.make Num Char) Char)
(Bytes.contains (Bytes.make Num Char) Char)
(Bytes.contains_from (Bytes.make Num Char) Num Char)
(Bytes.rcontains_from (Bytes.make Num Char) Num Char)

// Predicates
(Bytes.equal (Bytes.create Num) (Bytes.create Num))
(Bytes.equal (Bytes.make Num Char) (Bytes.make Num Char))
(Bytes.equal (Bytes.of_string Str) (Bytes.of_string Str))
(Bytes.starts_with (Bytes.make Num Char) (Bytes.make Num Char))
(Bytes.ends_with (Bytes.make Num Char) (Bytes.make Num Char))

// Higher-order
(Bytes.for_all (fun c1 -> ((=) c1 Char)) (Bytes.make Num Char))
(Bytes.exists (fun c2 -> ((=) c2 Char)) (Bytes.make Num Char))
(Bytes.map (fun c3 -> c3) (Bytes.make Num Char))
(Bytes.map Bytes.uppercase_ascii (Bytes.make Num Char))
(Bytes.mapi (fun i2 c4 -> c4) (Bytes.make Num Char))
(Bytes.iter print_char (Bytes.make Num Char))
(Bytes.fold_left (fun acc c5 -> acc) Num (Bytes.make Num Char))
(Bytes.fold_right (fun c6 acc -> acc) (Bytes.make Num Char) Num)

// Binary integer access
(Bytes.get_uint8 (Bytes.make Num Char) Num)
(Bytes.get_int8 (Bytes.make Num Char) Num)
(Bytes.get_uint16_ne (Bytes.make Num Char) Num)
(Bytes.get_uint16_be (Bytes.make Num Char) Num)
(Bytes.get_uint16_le (Bytes.make Num Char) Num)

// Chaining: outputs used as inputs
((=) (Bytes.length (Bytes.make Num Char)) Num)
((=) (Bytes.length (Bytes.of_string Str)) Num)
((<) (Bytes.length (Bytes.create Num)) Num)
(succ (Bytes.length (Bytes.make Num Char)))
(Bytes.sub (Bytes.make Num Char) Num (Bytes.length (Bytes.make Num Char)))
(Bytes.sub_string (Bytes.make Num Char) Num (Bytes.length (Bytes.make Num Char)))
(Bytes.extend (Bytes.create Num) Num (Bytes.length (Bytes.create Num)))

((=) (Bytes.get (Bytes.make Num Char) Num) Char)
(int_of_char (Bytes.get (Bytes.make Num Char) Num))
((=) (Bytes.to_string (Bytes.of_string Str)) Str)
((^) (Bytes.to_string (Bytes.make Num Char)) Str)
((^) (Bytes.to_string (Bytes.of_string Str)) (Bytes.to_string (Bytes.make Num Char)))
(Bytes.of_string (Bytes.to_string (Bytes.make Num Char)))
(Bytes.length (Bytes.to_string (Bytes.make Num Char)))

((=) (Bytes.index (Bytes.make Num Char) Char) Num)
(succ (Bytes.index (Bytes.make Num Char) Char))
(Bytes.get (Bytes.make Num Char) (Bytes.index (Bytes.make Num Char) Char))
(Bytes.contains_from (Bytes.make Num Char) (Bytes.index (Bytes.make Num Char) Char) Char)

(Bytes.copy (Bytes.cat (Bytes.make Num Char) (Bytes.make Num Char)))
(Bytes.length (Bytes.cat (Bytes.make Num Char) (Bytes.make Num Char)))
(Bytes.length (Bytes.uppercase_ascii (Bytes.make Num Char)))
(Bytes.equal (Bytes.copy (Bytes.make Num Char)) (Bytes.make Num Char))

((=) (Bytes.get_uint8 (Bytes.make Num Char) Num) Num)
(succ (Bytes.get_uint8 (Bytes.make Num Char) Num))

// Invalid
(Bytes.length Num)
(Bytes.get (Bytes.make Num Char) Str)
(Bytes.make Num Num)
(Bytes.cat (Bytes.make Num Char) Str)
(Bytes.equal (Bytes.make Num Char) Str)
(Bytes.index (Bytes.make Num Char) Num)
