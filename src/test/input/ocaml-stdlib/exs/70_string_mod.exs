// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 8_char.types, 10_strconv.types, 70_string_mod.types

// make: int -> char -> string
(String.make Num Char)

// empty: string constant
String.empty

// length: string -> int
(String.length Str)
(String.length String.empty)
(String.length (String.make Num Char))

// get: string -> int -> char
(String.get Str Num)
(String.get (String.make Num Char) Num)

// of_bytes, to_bytes
(String.of_bytes (Bytes.make Num Char))
(String.to_bytes Str)

// concat: string -> string list -> string
(String.concat Str (cons Str []))
(String.concat String.empty (cons Str []))

// cat: string -> string -> string
(String.cat Str Str)
(String.cat String.empty Str)
(String.cat Str String.empty)

// equal: t -> t -> bool
(String.equal Str Str)
(String.equal String.empty Str)

// compare: t -> t -> int
(String.compare Str Str)
(String.compare String.empty Str)

// contains: string -> char -> bool
(String.contains Str Char)
(String.contains (String.make Num Char) Char)

// sub: string -> int -> int -> string
(String.sub Str Num Num)
(String.sub (String.make Num Char) Num Num)

// split_on_char: char -> string -> string list
(String.split_on_char Char Str)
(String.split_on_char Char (String.make Num Char))

// map: (char -> char) -> string -> string
(String.map (fun c1 -> (chr (succ (code c1)))) Str)

// fold_left: ('acc -> char -> 'acc) -> 'acc -> string -> 'acc
(String.fold_left (fun acc1 c2 -> acc1) Str Str)

// for_all, exists: (char -> bool) -> string -> bool
(String.for_all (fun c3 -> ((=) c3 Char)) Str)
(String.exists (fun c4 -> ((=) c4 Char)) Str)

// trim, escaped, uppercase_ascii, lowercase_ascii, capitalize_ascii, uncapitalize_ascii
(String.trim Str)
(String.escaped Str)
(String.uppercase_ascii Str)
(String.lowercase_ascii Str)
(String.capitalize_ascii Str)
(String.uncapitalize_ascii Str)

// index, rindex: string -> char -> int
(String.index Str Char)
(String.rindex Str Char)

// index_opt, rindex_opt: string -> char -> int option
(String.index_opt Str Char)
(String.rindex_opt Str Char)

// index_from, rindex_from: string -> int -> char -> int
(String.index_from Str Num Char)
(String.rindex_from Str Num Char)

// starts_with, ends_with: prefix/suffix:string -> string -> bool
(String.starts_with Str Str)
(String.ends_with Str Str)

// hash: t -> int
(String.hash Str)
(String.hash String.empty)

// seeded_hash: int -> t -> int
(String.seeded_hash Num Str)

// is_valid_utf_8: t -> bool
(String.is_valid_utf_8 Str)

// edit_distance: t -> t -> int
(String.edit_distance Str Str)

// Chaining: make/cat/sub/trim return string — chain into more string ops
(String.length (String.make Num Char))
(String.length (String.cat Str Str))
(String.length (String.sub Str Num Num))
(String.length (String.trim Str))
(String.length (String.uppercase_ascii Str))
(String.get (String.make Num Char) Num)
(String.get (String.cat Str Str) Num)
(String.index (String.cat Str Str) Char)
(String.contains (String.uppercase_ascii Str) Char)
(String.equal (String.trim Str) Str)
(String.cat (String.trim Str) (String.escaped Str))
(String.cat (String.uppercase_ascii Str) (String.lowercase_ascii Str))
(String.sub (String.cat Str Str) Num (String.length Str))
(String.sub (String.trim Str) Num (String.length (String.trim Str)))
(String.hash (String.cat Str Str))
(String.hash (String.uppercase_ascii Str))

// length returns int — use in sub, get, seeded_hash, etc.
((=) (String.length Str) Num)
(succ (String.length Str))
((<) (String.length Str) Num)
(String.get Str (String.length Str))
(String.sub Str Num (String.length Str))
(String.seeded_hash (String.length Str) Str)
(String.index_from Str (String.length Str) Char)
((=) (String.length (String.cat Str Str)) Num)
((<) (String.length Str) (String.length (String.cat Str Str)))

// equal returns bool
((=) (String.equal Str Str) true)
(not (String.equal Str Str))
((&&) (String.equal Str Str) (String.equal String.empty String.empty))
((||) (String.equal Str Str) (String.contains Str Char))

// compare returns int
((=) (String.compare Str Str) Num)
(succ (String.compare Str Str))
((<) (String.compare Str Str) Num)

// contains/for_all/exists/starts_with/ends_with return bool
((=) (String.contains Str Char) true)
(not (String.contains Str Char))
(not (String.for_all (fun c5 -> ((=) c5 Char)) Str))
((&&) (String.contains Str Char) (String.exists (fun c6 -> ((=) c6 Char)) Str))
(not (String.starts_with Str Str))
(not (String.ends_with Str Str))

// index/rindex return int — use in sub, get
((=) (String.index Str Char) Num)
(succ (String.index Str Char))
(String.get Str (String.index Str Char))
(String.sub Str (String.index Str Char) Num)
(String.sub Str Num (String.rindex Str Char))

// hash/seeded_hash return int
((=) (String.hash Str) Num)
(succ (String.hash Str))
(String.seeded_hash (String.hash Str) Str)
((=) (String.seeded_hash Num Str) Num)

// split_on_char returns string list
((@) (String.split_on_char Char Str) (cons Str []))

// Invalid
(String.length Num)
(String.length Char)
(String.get Num Num)
(String.get Str Str)
(String.cat Num Str)
(String.cat Str Num)
(String.equal Str Num)
(String.contains Str Num)
(String.sub Str Char Num)
(String.hash Num)
(succ (String.equal Str Str))
(not (String.length Str))
