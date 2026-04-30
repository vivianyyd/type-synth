// 0_basics.types, 4_arith.types, 7_str.types, 9_unit.types

(ignore Num)
(ignore Str)
(ignore true)
(ignore false)
(ignore Char)
(ignore Unit)
(ignore (succ Num))
(ignore (+ Num Num))
(ignore (^ Str Str))
(ignore (ignore Num))

// ignore returns unit: unit can be passed to ignore again
(ignore (ignore (ignore Num)))
(ignore (ignore (ignore Str)))
(ignore (ignore true))

// ignore output (unit) can be passed to functions expecting unit
// (there are no such functions in this file besides ignore itself, shown above)
