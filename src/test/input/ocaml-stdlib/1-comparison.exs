// 0-basics.types, 1-comparison.types

(= Num Num)
(= Str Str)
(= true true)
(= Char Char)

(<> Num Num)
(<> Str Str)
(<> true false)

(< Num Num)
(< Str Str)

(> Num Num)
(> true false)

(<= Num Num)
(<= Str Str)

(>= Num Num)
(>= true false)

(compare Num Num)
(compare Str Str)
(compare true false)
(compare Char Char)

(min Num Num)
(min Str Str)

(max Num Num)
(max true false)

(== Num Num)
(== Str Str)

(!= Num Num)
(!= true false)

(= (min Num Num) Num)
(= (max Num Num) Num)
(= (compare Num Num) Num)
(< (compare Num Num) Num)
(> (compare Str Str) Num)
(min (compare Num Num) Num)
(max (compare Str Str) Num)

(= Num Str)
(= true Num)
(< Num Str)
(min Num Str)
(compare Num true)

// compare returns int: feed into arithmetic comparisons
(< (compare Num Num) Num)
(> (compare Num Num) Num)
(<= (compare Num Num) Num)
(>= (compare Num Num) Num)
(<> (compare Num Num) Num)
(compare (compare Num Num) Num)
(compare (compare Str Str) Num)
(compare (compare Num Num) (compare Str Str))
(min (compare Num Num) Num)
(max (compare Num Num) Num)
(min (compare Str Str) (compare Num Num))
(max (compare Num Num) (compare Str Str))
(min (compare Char Char) (compare Num Num))

// =, <>, <, >, <=, >= return bool: feed back into bool comparisons
(= (= Num Num) true)
(= (= Num Num) false)
(= (< Num Num) true)
(= (> Num Num) false)
(= (<= Num Num) (<= Num Num))
(= (>= Num Num) (>= Num Num))
(<> (= Num Num) false)
(<> (< Num Num) (<> Num Num))
(compare (= Num Num) true)
(compare (< Num Num) (> Num Num))
(compare (<= Num Num) (>= Num Num))
(compare (<> Num Num) (= Num Num))
(compare (= Str Str) (= Num Num))
(min (= Num Num) true)
(max (< Num Num) false)
(min (= Num Num) (< Num Num))
(max (<> Num Num) (>= Str Str))

// min/max return same type as inputs: feed back into comparisons
(= (min Num Num) Num)
(= (max Num Num) Num)
(= (min Str Str) Str)
(< (min Num Num) Num)
(< (min Num Num) (max Num Num))
(> (max Num Num) Num)
(> (max Num Num) (min Num Num))
(<= (min Num Num) (max Num Num))
(>= (max Num Num) (min Num Num))
(compare (min Num Num) (max Num Num))
(compare (max Str Str) (min Str Str))
(min (max Num Num) Num)
(max (min Num Num) Num)
(min (min Num Num) (max Num Num))
(max (max Num Num) (min Num Num))
(min (max Str Str) Str)
(max (min Str Str) Str)

// invalid: mixing output types across type boundaries
(min (compare Num Num) true)
(= (compare Num Num) Str)
(< (= Num Num) Num)
(min (max Num Num) Str)
(compare Num (min Str Str))
