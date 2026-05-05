// 0_basics.types, 2_boolean.types, 4_arith.types

// arithmetic output is not a boolean: cannot pass to not, &&, ||
(not (succ Num))
(not ((+) Num Num))
((&&) ((+) Num Num) true)
((&&) true ((-) Num Num))
((||) (( * ) Num Num) false)
((||) false (abs Num))
