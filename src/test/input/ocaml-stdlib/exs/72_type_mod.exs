// 0_basics.types, 1_comparison.types, 4_arith.types, 57_option_mod.types, 72_type_mod.types

// Id.make: unit -> 'a Id.t
(Type.Id.make Unit)

// Id.uid: 'a Id.t -> int
(Type.Id.uid (Type.Id.make Unit))

// Id.provably_equal: 'a Id.t -> 'b Id.t -> ('a, 'b) eq option
(Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit))

// Chaining: Id.make returns Id.t — use in uid and provably_equal
(Type.Id.uid (Type.Id.make Unit))
((=) (Type.Id.uid (Type.Id.make Unit)) Num)
(succ (Type.Id.uid (Type.Id.make Unit)))
((<) (Type.Id.uid (Type.Id.make Unit)) Num)
(Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit))

// uid returns int
((=) (Type.Id.uid (Type.Id.make Unit)) (Type.Id.uid (Type.Id.make Unit)))
(succ (Type.Id.uid (Type.Id.make Unit)))
((+) (Type.Id.uid (Type.Id.make Unit)) (Type.Id.uid (Type.Id.make Unit)))

// provably_equal returns an option — use is_some/is_none
(Option.is_some (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit)))
(Option.is_none (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit)))

// Invalid
(Type.Id.uid Num)
(Type.Id.uid Str)
(succ (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit)))
(not (Type.Id.uid (Type.Id.make Unit)))
