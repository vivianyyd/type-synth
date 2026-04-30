// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 8_char.types, 26_bytes_mod.types

// Construction
(create Num)
(make Num Char)
(init Num (fun i1 -> char_of_int i1))
(of_string Str)
(copy (create Num))
empty

// Inspection
(length (create Num))
(length (make Num Char))
(length empty)
(get (make Num Char) Num)

// Conversion
(to_string (create Num))
(to_string (make Num Char))
(to_string (of_string Str))
(unsafe_to_string (create Num))
(unsafe_of_string Str)

// Structural operations
(copy (make Num Char))
(copy (of_string Str))
(sub (make Num Char) Num Num)
(sub_string (make Num Char) Num Num)
(cat (create Num) (create Num))
(cat (make Num Char) (make Num Char))
(concat empty (cons (make Num Char) []))
(extend (create Num) Num Num)
(trim (make Num Char))
(escaped (make Num Char))
(uppercase_ascii (make Num Char))
(lowercase_ascii (make Num Char))
(capitalize_ascii (make Num Char))
(uncapitalize_ascii (make Num Char))

// Searching
(index (make Num Char) Char)
(index_opt (make Num Char) Char)
(rindex (make Num Char) Char)
(rindex_opt (make Num Char) Char)
(contains (make Num Char) Char)
(contains_from (make Num Char) Num Char)
(rcontains_from (make Num Char) Num Char)

// Predicates
(equal (create Num) (create Num))
(equal (make Num Char) (make Num Char))
(equal (of_string Str) (of_string Str))
(starts_with (make Num Char) (make Num Char))
(ends_with (make Num Char) (make Num Char))

// Higher-order
(for_all (fun c1 -> (= c1 Char)) (make Num Char))
(exists (fun c2 -> (= c2 Char)) (make Num Char))
(map (fun c3 -> c3) (make Num Char))
(map uppercase_ascii (make Num Char))
(mapi (fun i2 c4 -> c4) (make Num Char))
(iter print_char (make Num Char))
(fold_left (fun acc c5 -> acc) Num (make Num Char))
(fold_right (fun c6 acc -> acc) (make Num Char) Num)

// Binary integer access
(get_uint8 (make Num Char) Num)
(get_int8 (make Num Char) Num)
(get_uint16_ne (make Num Char) Num)
(get_uint16_be (make Num Char) Num)
(get_uint16_le (make Num Char) Num)

// Chaining: outputs used as inputs
(= (length (make Num Char)) Num)
(= (length (of_string Str)) Num)
(< (length (create Num)) Num)
(succ (length (make Num Char)))
(sub (make Num Char) Num (length (make Num Char)))
(sub_string (make Num Char) Num (length (make Num Char)))
(extend (create Num) Num (length (create Num)))

(= (get (make Num Char) Num) Char)
(int_of_char (get (make Num Char) Num))
(= (to_string (of_string Str)) Str)
(^ (to_string (make Num Char)) Str)
(^ (to_string (of_string Str)) (to_string (make Num Char)))
(of_string (to_string (make Num Char)))
(length (to_string (make Num Char)))

(= (index (make Num Char) Char) Num)
(succ (index (make Num Char) Char))
(get (make Num Char) (index (make Num Char) Char))
(contains_from (make Num Char) (index (make Num Char) Char) Char)

(copy (cat (make Num Char) (make Num Char)))
(length (cat (make Num Char) (make Num Char)))
(length (uppercase_ascii (make Num Char)))
(equal (copy (make Num Char)) (make Num Char))

(= (get_uint8 (make Num Char) Num) Num)
(succ (get_uint8 (make Num Char) Num))

// Invalid
(length Num)
(get (make Num Char) Str)
(make Num Num)
(cat (make Num Char) Str)
(equal (make Num Char) Str)
(index (make Num Char) Num)
