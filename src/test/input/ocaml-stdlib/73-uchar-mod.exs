// 0-basics.types, 1-comparison.types, 4-arith.types, 8-char.types, 73-uchar-mod.types

// Constants: min, max, bom, rep (all Uchar.t)
min
max
bom
rep

// succ, pred: t -> t
(succ min)
(pred max)
(succ bom)
(pred bom)

// of_int: int -> t
(of_int Num)

// to_int: t -> int
(to_int min)
(to_int max)
(to_int (of_int Num))

// is_valid: int -> bool
(is_valid Num)
(is_valid (to_int min))

// is_char: t -> bool
(is_char min)
(is_char (of_int Num))
(is_char bom)

// of_char: char -> t
(of_char Char)

// to_char: t -> char
(to_char (of_char Char))
(to_char min)

// equal: t -> t -> bool
(equal min max)
(equal bom rep)
(equal (of_int Num) (of_int Num))
(equal (of_char Char) (of_char Char))

// compare: t -> t -> int
(compare min max)
(compare (of_int Num) (of_int Num))

// hash: t -> int
(hash min)
(hash (of_int Num))

// seeded_hash: int -> t -> int
(seeded_hash Num min)
(seeded_hash Num (of_int Num))

// utf_decode: int -> t -> utf_decode
(utf_decode Num min)
(utf_decode Num (of_int Num))
(utf_decode Num (of_char Char))

// utf_decode_invalid: int -> utf_decode
(utf_decode_invalid Num)

// utf_decode_is_valid: utf_decode -> bool
(utf_decode_is_valid (utf_decode Num min))
(utf_decode_is_valid (utf_decode_invalid Num))

// utf_decode_uchar: utf_decode -> t
(utf_decode_uchar (utf_decode Num min))
(utf_decode_uchar (utf_decode Num (of_int Num)))

// utf_decode_length: utf_decode -> int
(utf_decode_length (utf_decode Num min))
(utf_decode_length (utf_decode_invalid Num))

// Chaining: of_int returns t — use in succ, pred, equal, compare, hash, to_int
(succ (of_int Num))
(pred (of_int Num))
(to_int (of_int Num))
(is_char (of_int Num))
(equal (of_int Num) min)
(compare (of_int Num) max)
(hash (of_int Num))
(utf_decode Num (of_int Num))

// to_int returns int — use in arithmetic and is_valid
(= (to_int min) Num)
(succ (to_int min))
(< (to_int min) (to_int max))
(+ (to_int min) (to_int max))
(is_valid (to_int min))
(is_valid (to_int (of_int Num)))
(of_int (to_int min))
(of_int (succ (to_int min)))

// succ/pred return t — chain again
(to_int (succ min))
(equal (succ min) (succ min))
(compare (succ min) (pred max))
(hash (succ min))
(is_char (succ min))

// of_char returns t — chain
(to_int (of_char Char))
(is_char (of_char Char))
(equal (of_char Char) (of_char Char))
(to_char (of_char Char))

// equal returns bool
(= (equal min max) false)
(not (equal min max))
(&& (equal min min) (equal max max))
(|| (equal min max) (is_char min))

// compare returns int
(= (compare min max) Num)
(succ (compare min max))
(< (compare min max) (compare max min))

// hash/seeded_hash return int
(= (hash min) Num)
(succ (hash min))
(seeded_hash (hash min) max)
(= (seeded_hash Num min) Num)

// utf_decode_is_valid returns bool
(= (utf_decode_is_valid (utf_decode Num min)) true)
(not (utf_decode_is_valid (utf_decode_invalid Num)))

// utf_decode_length returns int
(= (utf_decode_length (utf_decode Num min)) Num)
(succ (utf_decode_length (utf_decode Num min)))

// utf_decode_uchar returns t — chain into t ops
(to_int (utf_decode_uchar (utf_decode Num min)))
(is_char (utf_decode_uchar (utf_decode Num min)))
(equal (utf_decode_uchar (utf_decode Num min)) min)

// Invalid
(succ Num)
(of_int Char)
(to_int Num)
(is_char Num)
(is_char Char)
(equal Num min)
(equal min Num)
(utf_decode Num Num)
(utf_decode_is_valid Num)
(utf_decode_uchar Num)
(not (to_int min))
(succ (equal min max))
