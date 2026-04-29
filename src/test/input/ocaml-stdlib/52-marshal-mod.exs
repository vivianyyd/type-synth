// 0-basics.types, 1-comparison.types, 4-arith.types, 7-str.types, 13-io.types, 52-marshal-mod.types

// to_string: 'a -> extern_flags list -> string
(to_string Num [])
(to_string Str [])
(to_string true [])
(to_string Char [])

// from_string: string -> int -> 'a  (polymorphic output)
(from_string Str Num)

// from_channel: in_channel -> 'a  (polymorphic output)
(from_channel stdin)

// header_size: int constant
header_size

// data_size, total_size: bytes -> int -> int
(data_size (Bytes.make Num Char) Num)
(total_size (Bytes.make Num Char) Num)

// Chaining: to_string returns string — use in string ops
(= (to_string Num []) Str)
(^ (to_string Num []) Str)
(^ (to_string Str []) (to_string Num []))
(from_string (to_string Num []) Num)

// header_size is int — use in arithmetic
(= header_size Num)
(succ header_size)
(+ header_size Num)
(data_size (Bytes.make Num Char) header_size)
(total_size (Bytes.make Num Char) header_size)

// data_size / total_size return int
(= (data_size (Bytes.make Num Char) Num) Num)
(succ (data_size (Bytes.make Num Char) Num))
(< (data_size (Bytes.make Num Char) Num) (total_size (Bytes.make Num Char) Num))
(total_size (Bytes.make Num Char) (data_size (Bytes.make Num Char) Num))

// Invalid: wrong output types used in wrong contexts
(succ (to_string Num []))
(not (to_string Num []))
(^ header_size Str)
(not (data_size (Bytes.make Num Char) Num))
(to_string Num Num)
