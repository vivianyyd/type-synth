// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 13_io.types, 17_out.types, 18_in.types, 31_digest_mod.types

// Constructing digests
(Digest.string Str)
(Digest.substring Str Num Num)
(Digest.of_hex Str)
(Digest.from_hex Str)
(Digest.file Str)
(Digest.input stdin)
(Digest.channel stdin Num)

// compare: t -> t -> int
(Digest.compare (Digest.string Str) (Digest.string Str))
(Digest.compare (Digest.of_hex Str) (Digest.from_hex Str))

// equal: t -> t -> bool
(Digest.equal (Digest.string Str) (Digest.string Str))
(Digest.equal (Digest.of_hex Str) (Digest.from_hex Str))

// to_hex: t -> string
(Digest.to_hex (Digest.string Str))
(Digest.to_hex (Digest.of_hex Str))
(Digest.to_hex (Digest.file Str))
(Digest.to_hex (Digest.input stdin))

// output: out_channel -> t -> unit
(Digest.output stdout (Digest.string Str))
(Digest.output stdout (Digest.of_hex Str))
(Digest.output stderr (Digest.string Str))

// Chaining: outputs used as inputs

// string, file, of_hex produce t: use in compare/equal/to_hex
(Digest.equal (Digest.string Str) (Digest.file Str))
(Digest.compare (Digest.string Str) (Digest.file Str))
(Digest.compare (Digest.of_hex Str) (Digest.string Str))
(Digest.equal (Digest.from_hex (Digest.to_hex (Digest.string Str))) (Digest.string Str))

// to_hex returns string: use in string operations and re-parsing
((=) (Digest.to_hex (Digest.string Str)) Str)
((^) (Digest.to_hex (Digest.string Str)) Str)
((^) (Digest.to_hex (Digest.string Str)) (Digest.to_hex (Digest.of_hex Str)))
(Digest.from_hex (Digest.to_hex (Digest.string Str)))
(Digest.of_hex (Digest.to_hex (Digest.string Str)))
(Digest.string (Digest.to_hex (Digest.string Str)))
(Digest.equal (Digest.from_hex (Digest.to_hex (Digest.string Str))) (Digest.of_hex (Digest.to_hex (Digest.string Str))))

// compare returns int: use in arithmetic/comparisons
((=) (Digest.compare (Digest.string Str) (Digest.string Str)) Num)
((<) (Digest.compare (Digest.string Str) (Digest.string Str)) Num)
(succ (Digest.compare (Digest.string Str) (Digest.string Str)))

// equal returns bool
((=) (Digest.equal (Digest.string Str) (Digest.string Str)) true)

// substring and channel
(Digest.equal (Digest.substring Str Num Num) (Digest.string Str))
(Digest.to_hex (Digest.substring Str Num Num))
(Digest.to_hex (Digest.channel stdin Num))

// Invalid
(Digest.to_hex Str)
(Digest.compare Str (Digest.string Str))
(Digest.equal Str (Digest.of_hex Str))
(Digest.string Num)
(Digest.of_hex Num)
