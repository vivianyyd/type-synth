// 0_basics.types, 1_comparison.types, 4_arith.types, 36_ephemeron_mod.types

// K1: one-key ephemerons
(Ephemeron.K1.make Num Str)
(Ephemeron.K1.make Str Num)
(Ephemeron.K1.make Num Num)
(Ephemeron.K1.make Str Str)
(Ephemeron.K1.make true Num)
(Ephemeron.K1.make Num true)

(Ephemeron.K1.query (Ephemeron.K1.make Num Str) Num)
(Ephemeron.K1.query (Ephemeron.K1.make Str Num) Str)
(Ephemeron.K1.query (Ephemeron.K1.make Num Num) Num)
(Ephemeron.K1.query (Ephemeron.K1.make true Str) true)

// K1.Bucket
(Ephemeron.K1.Bucket.make Unit)
(Ephemeron.K1.Bucket.add (Ephemeron.K1.Bucket.make Unit) Num Str)
(Ephemeron.K1.Bucket.add (Ephemeron.K1.Bucket.make Unit) Str Num)
(Ephemeron.K1.Bucket.add (Ephemeron.K1.Bucket.make Unit) Num Num)
(Ephemeron.K1.Bucket.remove (Ephemeron.K1.Bucket.make Unit) Num)
(Ephemeron.K1.Bucket.find (Ephemeron.K1.Bucket.make Unit) Num)
(Ephemeron.K1.Bucket.find (Ephemeron.K1.Bucket.make Unit) Str)
(Ephemeron.K1.Bucket.length (Ephemeron.K1.Bucket.make Unit))
(Ephemeron.K1.Bucket.clear (Ephemeron.K1.Bucket.make Unit))

// K2: two-key ephemerons
(Ephemeron.K2.make Num Str true)
(Ephemeron.K2.make Str Num false)
(Ephemeron.K2.make Num Num Num)
(Ephemeron.K2.make Str Str Str)

(Ephemeron.K2.query (Ephemeron.K2.make Num Str true) Num Str)
(Ephemeron.K2.query (Ephemeron.K2.make Str Num false) Str Num)

// K2.Bucket
(Ephemeron.K2.Bucket.make Unit)
(Ephemeron.K2.Bucket.add (Ephemeron.K2.Bucket.make Unit) Num Str true)
(Ephemeron.K2.Bucket.remove (Ephemeron.K2.Bucket.make Unit) Num Str)
(Ephemeron.K2.Bucket.find (Ephemeron.K2.Bucket.make Unit) Num Str)
(Ephemeron.K2.Bucket.length (Ephemeron.K2.Bucket.make Unit))
(Ephemeron.K2.Bucket.clear (Ephemeron.K2.Bucket.make Unit))

// Kn: n-key ephemerons (key is 'k array)
(Ephemeron.Kn.make (Array.make Num Num) Str)
(Ephemeron.Kn.make (Array.make Num Str) Num)
(Ephemeron.Kn.query (Ephemeron.Kn.make (Array.make Num Num) Str) (Array.make Num Num))

// Kn.Bucket
(Ephemeron.Kn.Bucket.make Unit)
(Ephemeron.Kn.Bucket.add (Ephemeron.Kn.Bucket.make Unit) (Array.make Num Num) Str)
(Ephemeron.Kn.Bucket.find (Ephemeron.Kn.Bucket.make Unit) (Array.make Num Num))
(Ephemeron.Kn.Bucket.length (Ephemeron.Kn.Bucket.make Unit))
(Ephemeron.Kn.Bucket.clear (Ephemeron.Kn.Bucket.make Unit))

// Chaining: K1.Bucket.length returns int
((=) (Ephemeron.K1.Bucket.length (Ephemeron.K1.Bucket.make Unit)) Num)
(succ (Ephemeron.K1.Bucket.length (Ephemeron.K1.Bucket.make Unit)))
((<) (Ephemeron.K1.Bucket.length (Ephemeron.K1.Bucket.make Unit)) Num)

// K2.Bucket.length returns int
((=) (Ephemeron.K2.Bucket.length (Ephemeron.K2.Bucket.make Unit)) Num)
(succ (Ephemeron.K2.Bucket.length (Ephemeron.K2.Bucket.make Unit)))

// Kn.Bucket.length returns int
((=) (Ephemeron.Kn.Bucket.length (Ephemeron.Kn.Bucket.make Unit)) Num)

// K1.query returns 'b option: use in comparisons
((=) (Ephemeron.K1.query (Ephemeron.K1.make Num Str) Num) (Ephemeron.K1.query (Ephemeron.K1.make Num Str) Num))

// K1.Bucket.find returns 'd option
((=) (Ephemeron.K1.Bucket.find (Ephemeron.K1.Bucket.make Unit) Num) (Ephemeron.K1.Bucket.find (Ephemeron.K1.Bucket.make Unit) Num))

// Invalid
(Ephemeron.K1.query (Ephemeron.K1.make Num Str) Str)
(Ephemeron.K1.Bucket.add (Ephemeron.K1.Bucket.make Unit) Num Str Num)
(Ephemeron.K1.Bucket.length Num)
(Ephemeron.K2.query (Ephemeron.K2.make Num Str true) Str Num)
