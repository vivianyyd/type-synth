// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 74_unit_mod.types

// equal: t -> t -> bool
(Unit.equal Unit Unit)

// compare: t -> t -> int
(Unit.compare Unit Unit)

// to_string: t -> string
(Unit.to_string Unit)

// Chaining: equal returns bool
((=) (Unit.equal Unit Unit) true)
(not (Unit.equal Unit Unit))
((&&) (Unit.equal Unit Unit) (Unit.equal Unit Unit))

// compare returns int
((=) (Unit.compare Unit Unit) Num)
(succ (Unit.compare Unit Unit))
((<) (Unit.compare Unit Unit) Num)

// to_string returns string
((=) (Unit.to_string Unit) Str)
((^) (Unit.to_string Unit) Str)
((^) (Unit.to_string Unit) (Unit.to_string Unit))

// Invalid
(Unit.equal Num Unit)
(Unit.equal Unit Num)
(Unit.equal Str Str)
(Unit.compare Num Unit)
(Unit.to_string Num)
(succ (Unit.equal Unit Unit))
(not (Unit.compare Unit Unit))
