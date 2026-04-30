// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 13_io.types, 52_marshal_mod.types

// to_string: 'a -> extern_flags list -> string
(Marshal.to_string Num [])
(Marshal.to_string Str [])
(Marshal.to_string true [])
(Marshal.to_string Char [])

// from_string: string -> int -> 'a  (polymorphic output)
(Marshal.from_string Str Num)

// from_channel: in_channel -> 'a  (polymorphic output)
(Marshal.from_channel stdin)

// header_size: int constant
Marshal.header_size

// data_size, total_size: bytes -> int -> int
(Marshal.data_size (Bytes.make Num Char) Num)
(Marshal.total_size (Bytes.make Num Char) Num)

// Chaining: to_string returns string — use in string ops
((=) (Marshal.to_string Num []) Str)
((^) (Marshal.to_string Num []) Str)
((^) (Marshal.to_string Str []) (Marshal.to_string Num []))
(Marshal.from_string (Marshal.to_string Num []) Num)

// header_size is int — use in arithmetic
((=) Marshal.header_size Num)
(succ Marshal.header_size)
((+) Marshal.header_size Num)
(Marshal.data_size (Bytes.make Num Char) Marshal.header_size)
(Marshal.total_size (Bytes.make Num Char) Marshal.header_size)

// data_size / total_size return int
((=) (Marshal.data_size (Bytes.make Num Char) Num) Num)
(succ (Marshal.data_size (Bytes.make Num Char) Num))
((<) (Marshal.data_size (Bytes.make Num Char) Num) (Marshal.total_size (Bytes.make Num Char) Num))
(Marshal.total_size (Bytes.make Num Char) (Marshal.data_size (Bytes.make Num Char) Num))

// Invalid: wrong output types used in wrong contexts
(succ (Marshal.to_string Num []))
(not (Marshal.to_string Num []))
((^) Marshal.header_size Str)
(not (Marshal.data_size (Bytes.make Num Char) Num))
(Marshal.to_string Num Num)
