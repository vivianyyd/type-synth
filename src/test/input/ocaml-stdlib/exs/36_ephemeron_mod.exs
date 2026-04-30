// 0_basics.types, 1_comparison.types, 4_arith.types, 36_ephemeron_mod.types

// K1: one-key ephemerons
(K1.make Num Str)
(K1.make Str Num)
(K1.make Num Num)
(K1.make Str Str)
(K1.make true Num)
(K1.make Num true)

(K1.query (K1.make Num Str) Num)
(K1.query (K1.make Str Num) Str)
(K1.query (K1.make Num Num) Num)
(K1.query (K1.make true Str) true)

// K1.Bucket
(K1.Bucket.make Unit)
(K1.Bucket.add (K1.Bucket.make Unit) Num Str)
(K1.Bucket.add (K1.Bucket.make Unit) Str Num)
(K1.Bucket.add (K1.Bucket.make Unit) Num Num)
(K1.Bucket.remove (K1.Bucket.make Unit) Num)
(K1.Bucket.find (K1.Bucket.make Unit) Num)
(K1.Bucket.find (K1.Bucket.make Unit) Str)
(K1.Bucket.length (K1.Bucket.make Unit))
(K1.Bucket.clear (K1.Bucket.make Unit))

// K2: two-key ephemerons
(K2.make Num Str true)
(K2.make Str Num false)
(K2.make Num Num Num)
(K2.make Str Str Str)

(K2.query (K2.make Num Str true) Num Str)
(K2.query (K2.make Str Num false) Str Num)

// K2.Bucket
(K2.Bucket.make Unit)
(K2.Bucket.add (K2.Bucket.make Unit) Num Str true)
(K2.Bucket.remove (K2.Bucket.make Unit) Num Str)
(K2.Bucket.find (K2.Bucket.make Unit) Num Str)
(K2.Bucket.length (K2.Bucket.make Unit))
(K2.Bucket.clear (K2.Bucket.make Unit))

// Kn: n-key ephemerons (key is 'k array)
(Kn.make (Array.make Num Num) Str)
(Kn.make (Array.make Num Str) Num)
(Kn.query (Kn.make (Array.make Num Num) Str) (Array.make Num Num))

// Kn.Bucket
(Kn.Bucket.make Unit)
(Kn.Bucket.add (Kn.Bucket.make Unit) (Array.make Num Num) Str)
(Kn.Bucket.find (Kn.Bucket.make Unit) (Array.make Num Num))
(Kn.Bucket.length (Kn.Bucket.make Unit))
(Kn.Bucket.clear (Kn.Bucket.make Unit))

// Chaining: K1.Bucket.length returns int
(= (K1.Bucket.length (K1.Bucket.make Unit)) Num)
(succ (K1.Bucket.length (K1.Bucket.make Unit)))
(< (K1.Bucket.length (K1.Bucket.make Unit)) Num)

// K2.Bucket.length returns int
(= (K2.Bucket.length (K2.Bucket.make Unit)) Num)
(succ (K2.Bucket.length (K2.Bucket.make Unit)))

// Kn.Bucket.length returns int
(= (Kn.Bucket.length (Kn.Bucket.make Unit)) Num)

// K1.query returns 'b option: use in comparisons
(= (K1.query (K1.make Num Str) Num) (K1.query (K1.make Num Str) Num))

// K1.Bucket.find returns 'd option
(= (K1.Bucket.find (K1.Bucket.make Unit) Num) (K1.Bucket.find (K1.Bucket.make Unit) Num))

// Invalid
(K1.query (K1.make Num Str) Str)
(K1.Bucket.add (K1.Bucket.make Unit) Num Str Num)
(K1.Bucket.length Num)
(K2.query (K2.make Num Str true) Str Num)
