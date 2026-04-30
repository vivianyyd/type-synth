// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 8_char.types, 10_strconv.types, 70_string_mod.types

// make: int -> char -> string
(make Num Char)

// empty: string constant
empty

// length: string -> int
(length Str)
(length empty)
(length (make Num Char))

// get: string -> int -> char
(get Str Num)
(get (make Num Char) Num)

// of_bytes, to_bytes
(of_bytes (Bytes.make Num Char))
(to_bytes Str)

// concat: string -> string list -> string
(concat Str (cons Str []))
(concat empty (cons Str []))

// cat: string -> string -> string
(cat Str Str)
(cat empty Str)
(cat Str empty)

// equal: t -> t -> bool
(equal Str Str)
(equal empty Str)

// compare: t -> t -> int
(compare Str Str)
(compare empty Str)

// contains: string -> char -> bool
(contains Str Char)
(contains (make Num Char) Char)

// sub: string -> int -> int -> string
(sub Str Num Num)
(sub (make Num Char) Num Num)

// split_on_char: char -> string -> string list
(split_on_char Char Str)
(split_on_char Char (make Num Char))

// map: (char -> char) -> string -> string
(map (fun c1 -> (chr (succ (code c1)))) Str)

// fold_left: ('acc -> char -> 'acc) -> 'acc -> string -> 'acc
(fold_left (fun acc1 c2 -> acc1) Str Str)

// for_all, exists: (char -> bool) -> string -> bool
(for_all (fun c3 -> (= c3 Char)) Str)
(exists (fun c4 -> (= c4 Char)) Str)

// trim, escaped, uppercase_ascii, lowercase_ascii, capitalize_ascii, uncapitalize_ascii
(trim Str)
(escaped Str)
(uppercase_ascii Str)
(lowercase_ascii Str)
(capitalize_ascii Str)
(uncapitalize_ascii Str)

// index, rindex: string -> char -> int
(index Str Char)
(rindex Str Char)

// index_opt, rindex_opt: string -> char -> int option
(index_opt Str Char)
(rindex_opt Str Char)

// index_from, rindex_from: string -> int -> char -> int
(index_from Str Num Char)
(rindex_from Str Num Char)

// starts_with, ends_with: prefix/suffix:string -> string -> bool
(starts_with Str Str)
(ends_with Str Str)

// hash: t -> int
(hash Str)
(hash empty)

// seeded_hash: int -> t -> int
(seeded_hash Num Str)

// is_valid_utf_8: t -> bool
(is_valid_utf_8 Str)

// edit_distance: t -> t -> int
(edit_distance Str Str)

// Chaining: make/cat/sub/trim return string — chain into more string ops
(length (make Num Char))
(length (cat Str Str))
(length (sub Str Num Num))
(length (trim Str))
(length (uppercase_ascii Str))
(get (make Num Char) Num)
(get (cat Str Str) Num)
(index (cat Str Str) Char)
(contains (uppercase_ascii Str) Char)
(equal (trim Str) Str)
(cat (trim Str) (escaped Str))
(cat (uppercase_ascii Str) (lowercase_ascii Str))
(sub (cat Str Str) Num (length Str))
(sub (trim Str) Num (length (trim Str)))
(hash (cat Str Str))
(hash (uppercase_ascii Str))

// length returns int — use in sub, get, seeded_hash, etc.
(= (length Str) Num)
(succ (length Str))
(< (length Str) Num)
(get Str (length Str))
(sub Str Num (length Str))
(seeded_hash (length Str) Str)
(index_from Str (length Str) Char)
(= (length (cat Str Str)) Num)
(< (length Str) (length (cat Str Str)))

// equal returns bool
(= (equal Str Str) true)
(not (equal Str Str))
(&& (equal Str Str) (equal empty empty))
(|| (equal Str Str) (contains Str Char))

// compare returns int
(= (compare Str Str) Num)
(succ (compare Str Str))
(< (compare Str Str) Num)

// contains/for_all/exists/starts_with/ends_with return bool
(= (contains Str Char) true)
(not (contains Str Char))
(not (for_all (fun c5 -> (= c5 Char)) Str))
(&& (contains Str Char) (exists (fun c6 -> (= c6 Char)) Str))
(not (starts_with Str Str))
(not (ends_with Str Str))

// index/rindex return int — use in sub, get
(= (index Str Char) Num)
(succ (index Str Char))
(get Str (index Str Char))
(sub Str (index Str Char) Num)
(sub Str Num (rindex Str Char))

// hash/seeded_hash return int
(= (hash Str) Num)
(succ (hash Str))
(seeded_hash (hash Str) Str)
(= (seeded_hash Num Str) Num)

// split_on_char returns string list
(@ (split_on_char Char Str) (cons Str []))

// Invalid
(length Num)
(length Char)
(get Num Num)
(get Str Str)
(cat Num Str)
(cat Str Num)
(equal Str Num)
(contains Str Num)
(sub Str Char Num)
(hash Num)
(succ (equal Str Str))
(not (length Str))
