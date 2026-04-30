// 0_basics.types, 1_comparison.types, 4_arith.types, 8_char.types, 73_uchar_mod.types

// Constants: min, max, bom, rep (all Uchar.t)
Uchar.min
Uchar.max
Uchar.bom
Uchar.rep

// succ, pred: t -> t
(Uchar.succ Uchar.min)
(Uchar.pred Uchar.max)
(Uchar.succ Uchar.bom)
(Uchar.pred Uchar.bom)

// of_int: int -> t
(Uchar.of_int Num)

// to_int: t -> int
(Uchar.to_int Uchar.min)
(Uchar.to_int Uchar.max)
(Uchar.to_int (Uchar.of_int Num))

// is_valid: int -> bool
(Uchar.is_valid Num)
(Uchar.is_valid (Uchar.to_int Uchar.min))

// is_char: t -> bool
(Uchar.is_char Uchar.min)
(Uchar.is_char (Uchar.of_int Num))
(Uchar.is_char Uchar.bom)

// of_char: char -> t
(Uchar.of_char Char)

// to_char: t -> char
(Uchar.to_char (Uchar.of_char Char))
(Uchar.to_char Uchar.min)

// equal: t -> t -> bool
(Uchar.equal Uchar.min Uchar.max)
(Uchar.equal Uchar.bom Uchar.rep)
(Uchar.equal (Uchar.of_int Num) (Uchar.of_int Num))
(Uchar.equal (Uchar.of_char Char) (Uchar.of_char Char))

// compare: t -> t -> int
(Uchar.compare Uchar.min Uchar.max)
(Uchar.compare (Uchar.of_int Num) (Uchar.of_int Num))

// hash: t -> int
(Uchar.hash Uchar.min)
(Uchar.hash (Uchar.of_int Num))

// seeded_hash: int -> t -> int
(Uchar.seeded_hash Num Uchar.min)
(Uchar.seeded_hash Num (Uchar.of_int Num))

// utf_decode: int -> t -> utf_decode
(Uchar.utf_decode Num Uchar.min)
(Uchar.utf_decode Num (Uchar.of_int Num))
(Uchar.utf_decode Num (Uchar.of_char Char))

// utf_decode_invalid: int -> utf_decode
(Uchar.utf_decode_invalid Num)

// utf_decode_is_valid: utf_decode -> bool
(Uchar.utf_decode_is_valid (Uchar.utf_decode Num Uchar.min))
(Uchar.utf_decode_is_valid (Uchar.utf_decode_invalid Num))

// utf_decode_uchar: utf_decode -> t
(Uchar.utf_decode_uchar (Uchar.utf_decode Num Uchar.min))
(Uchar.utf_decode_uchar (Uchar.utf_decode Num (Uchar.of_int Num)))

// utf_decode_length: utf_decode -> int
(Uchar.utf_decode_length (Uchar.utf_decode Num Uchar.min))
(Uchar.utf_decode_length (Uchar.utf_decode_invalid Num))

// Chaining: of_int returns t — use in succ, pred, equal, compare, hash, to_int
(Uchar.succ (Uchar.of_int Num))
(Uchar.pred (Uchar.of_int Num))
(Uchar.to_int (Uchar.of_int Num))
(Uchar.is_char (Uchar.of_int Num))
(Uchar.equal (Uchar.of_int Num) Uchar.min)
(Uchar.compare (Uchar.of_int Num) Uchar.max)
(Uchar.hash (Uchar.of_int Num))
(Uchar.utf_decode Num (Uchar.of_int Num))

// to_int returns int — use in arithmetic and is_valid
((=) (Uchar.to_int Uchar.min) Num)
(Uchar.succ (Uchar.to_int Uchar.min))
((<) (Uchar.to_int Uchar.min) (Uchar.to_int Uchar.max))
((+) (Uchar.to_int Uchar.min) (Uchar.to_int Uchar.max))
(Uchar.is_valid (Uchar.to_int Uchar.min))
(Uchar.is_valid (Uchar.to_int (Uchar.of_int Num)))
(Uchar.of_int (Uchar.to_int Uchar.min))
(Uchar.of_int (Uchar.succ (Uchar.to_int Uchar.min)))

// succ/pred return t — chain again
(Uchar.to_int (Uchar.succ Uchar.min))
(Uchar.equal (Uchar.succ Uchar.min) (Uchar.succ Uchar.min))
(Uchar.compare (Uchar.succ Uchar.min) (Uchar.pred Uchar.max))
(Uchar.hash (Uchar.succ Uchar.min))
(Uchar.is_char (Uchar.succ Uchar.min))

// of_char returns t — chain
(Uchar.to_int (Uchar.of_char Char))
(Uchar.is_char (Uchar.of_char Char))
(Uchar.equal (Uchar.of_char Char) (Uchar.of_char Char))
(Uchar.to_char (Uchar.of_char Char))

// equal returns bool
((=) (Uchar.equal Uchar.min Uchar.max) false)
(not (Uchar.equal Uchar.min Uchar.max))
((&&) (Uchar.equal Uchar.min Uchar.min) (Uchar.equal Uchar.max Uchar.max))
((||) (Uchar.equal Uchar.min Uchar.max) (Uchar.is_char Uchar.min))

// compare returns int
((=) (Uchar.compare Uchar.min Uchar.max) Num)
(Uchar.succ (Uchar.compare Uchar.min Uchar.max))
((<) (Uchar.compare Uchar.min Uchar.max) (Uchar.compare Uchar.max Uchar.min))

// hash/seeded_hash return int
((=) (Uchar.hash Uchar.min) Num)
(Uchar.succ (Uchar.hash Uchar.min))
(Uchar.seeded_hash (Uchar.hash Uchar.min) Uchar.max)
((=) (Uchar.seeded_hash Num Uchar.min) Num)

// utf_decode_is_valid returns bool
((=) (Uchar.utf_decode_is_valid (Uchar.utf_decode Num Uchar.min)) true)
(not (Uchar.utf_decode_is_valid (Uchar.utf_decode_invalid Num)))

// utf_decode_length returns int
((=) (Uchar.utf_decode_length (Uchar.utf_decode Num Uchar.min)) Num)
(Uchar.succ (Uchar.utf_decode_length (Uchar.utf_decode Num Uchar.min)))

// utf_decode_uchar returns t — chain into t ops
(Uchar.to_int (Uchar.utf_decode_uchar (Uchar.utf_decode Num Uchar.min)))
(Uchar.is_char (Uchar.utf_decode_uchar (Uchar.utf_decode Num Uchar.min)))
(Uchar.equal (Uchar.utf_decode_uchar (Uchar.utf_decode Num Uchar.min)) Uchar.min)

// Invalid
(Uchar.succ Num)
(Uchar.of_int Char)
(Uchar.to_int Num)
(Uchar.is_char Num)
(Uchar.is_char Char)
(Uchar.equal Num Uchar.min)
(Uchar.equal Uchar.min Num)
(Uchar.utf_decode Num Num)
(Uchar.utf_decode_is_valid Num)
(Uchar.utf_decode_uchar Num)
(not (Uchar.to_int Uchar.min))
(Uchar.succ (Uchar.equal Uchar.min Uchar.max))
