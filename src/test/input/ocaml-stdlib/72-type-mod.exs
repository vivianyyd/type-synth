// 0-basics.types, 1-comparison.types, 4-arith.types, 57-option-mod.types, 72-type-mod.types

// Id.make: unit -> 'a Id.t
(Id.make Unit)

// Id.uid: 'a Id.t -> int
(Id.uid (Id.make Unit))

// Id.provably_equal: 'a Id.t -> 'b Id.t -> ('a, 'b) eq option
(Id.provably_equal (Id.make Unit) (Id.make Unit))

// Chaining: Id.make returns Id.t — use in uid and provably_equal
(Id.uid (Id.make Unit))
(= (Id.uid (Id.make Unit)) Num)
(succ (Id.uid (Id.make Unit)))
(< (Id.uid (Id.make Unit)) Num)
(Id.provably_equal (Id.make Unit) (Id.make Unit))

// uid returns int
(= (Id.uid (Id.make Unit)) (Id.uid (Id.make Unit)))
(succ (Id.uid (Id.make Unit)))
(+ (Id.uid (Id.make Unit)) (Id.uid (Id.make Unit)))

// provably_equal returns an option — use is_some/is_none
(is_some (Id.provably_equal (Id.make Unit) (Id.make Unit)))
(is_none (Id.provably_equal (Id.make Unit) (Id.make Unit)))

// Invalid
(Id.uid Num)
(Id.uid Str)
(succ (Id.provably_equal (Id.make Unit) (Id.make Unit)))
(not (Id.uid (Id.make Unit)))
