// 0-basics.types, 2-boolean.types

(not true)
(not false)

(&& true true)
(&& true false)
(&& false false)

(|| true false)
(|| false false)
(|| true true)

(not (not true))
(not (&& true false))
(&& (not true) (not false))
(|| (&& true false) (not false))
(&& (|| true false) (|| false true))
(not (|| false false))

(not Num)
(&& true Num)
(|| Str false)
(&& Num Str)

// not returns bool: feed into &&, ||, not
(not (not (not true)))
(not (not (not false)))
(&& (not true) true)
(&& true (not false))
(|| (not false) false)
(|| false (not true))
(&& (not true) (not true))
(|| (not false) (not false))
(not (&& (not true) (not false)))
(not (|| (not true) (not false)))

// && returns bool: feed into not, ||, &&
(&& (&& true false) true)
(&& true (&& false true))
(|| (&& true true) false)
(|| false (&& true false))
(not (&& (&& true false) (|| true false)))
(&& (&& true true) (&& false false))
(|| (&& true false) (&& false true))

// || returns bool: feed into not, &&, ||
(|| (|| true false) true)
(|| false (|| false true))
(&& (|| true false) true)
(&& true (|| false false))
(not (|| (|| false false) (|| false false)))
(|| (|| true false) (|| false true))
(&& (|| true false) (|| false true))

// deeper chains
(not (&& (|| true false) (not (&& true false))))
(&& (not (|| false false)) (|| (not true) (not false)))
(|| (&& (not false) true) (&& true (not true)))

// invalid
(not Num)
(&& (not true) Num)
(|| Str (not false))
