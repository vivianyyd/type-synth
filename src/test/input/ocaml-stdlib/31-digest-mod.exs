// 0-basics.types, 1-comparison.types, 4-arith.types, 7-str.types, 13-io.types, 17-out.types, 18-in.types, 31-digest-mod.types

// Constructing digests
(string Str)
(substring Str Num Num)
(of_hex Str)
(from_hex Str)
(file Str)
(input stdin)
(channel stdin Num)

// compare: t -> t -> int
(compare (string Str) (string Str))
(compare (of_hex Str) (from_hex Str))

// equal: t -> t -> bool
(equal (string Str) (string Str))
(equal (of_hex Str) (from_hex Str))

// to_hex: t -> string
(to_hex (string Str))
(to_hex (of_hex Str))
(to_hex (file Str))
(to_hex (input stdin))

// output: out_channel -> t -> unit
(output stdout (string Str))
(output stdout (of_hex Str))
(output stderr (string Str))

// Chaining: outputs used as inputs

// string, file, of_hex produce t: use in compare/equal/to_hex
(equal (string Str) (file Str))
(compare (string Str) (file Str))
(compare (of_hex Str) (string Str))
(equal (from_hex (to_hex (string Str))) (string Str))

// to_hex returns string: use in string operations and re-parsing
(= (to_hex (string Str)) Str)
(^ (to_hex (string Str)) Str)
(^ (to_hex (string Str)) (to_hex (of_hex Str)))
(from_hex (to_hex (string Str)))
(of_hex (to_hex (string Str)))
(string (to_hex (string Str)))
(equal (from_hex (to_hex (string Str))) (of_hex (to_hex (string Str))))

// compare returns int: use in arithmetic/comparisons
(= (compare (string Str) (string Str)) Num)
(< (compare (string Str) (string Str)) Num)
(succ (compare (string Str) (string Str)))

// equal returns bool
(= (equal (string Str) (string Str)) true)

// substring and channel
(equal (substring Str Num Num) (string Str))
(to_hex (substring Str Num Num))
(to_hex (channel stdin Num))

// Invalid
(to_hex Str)
(compare Str (string Str))
(equal Str (of_hex Str))
(string Num)
(of_hex Num)
