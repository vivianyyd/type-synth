// 0_basics.types, 1_comparison.types, 2_boolean.types, 4_arith.types, 7_str.types, 9_unit.types, 57_option_mod.types, 72_type_mod.types

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

// ---- Parameters, results and the Id.t type, one by one

// make takes unit (last argument wrong)
(Type.Id.make Num)
(Type.Id.make Str)
(Type.Id.make true)

// make returns an Id.t: positive where one is needed, negative elsewhere
((=) (Type.Id.make Unit) (Type.Id.make Unit))
(Option.some (Type.Id.make Unit))
(Option.value (Option.some (Type.Id.make Unit)) (Type.Id.make Unit))
(Option.is_some (Option.some (Type.Id.make Unit)))
(succ (Type.Id.make Unit))
((^) Str (Type.Id.make Unit))
((=) Num (Type.Id.make Unit))
((=) Str (Type.Id.make Unit))
((=) true (Type.Id.make Unit))
((=) Unit (Type.Id.make Unit))
((=) (Option.some Num) (Type.Id.make Unit))
(Option.value (Option.some Num) (Type.Id.make Unit))
(Option.value (Option.some Str) (Type.Id.make Unit))

// uid takes an Id.t and returns int
(Type.Id.uid (Option.value (Option.some (Type.Id.make Unit)) (Type.Id.make Unit)))
(Type.Id.uid Unit)
(Type.Id.uid true)
(Type.Id.uid (Option.some Num))
(Type.Id.uid (Option.some (Type.Id.make Unit)))
((^) Str (Type.Id.uid (Type.Id.make Unit)))
((=) Str (Type.Id.uid (Type.Id.make Unit)))
((=) true (Type.Id.uid (Type.Id.make Unit)))
((=) Unit (Type.Id.uid (Type.Id.make Unit)))
((=) Num (Type.Id.uid (Type.Id.make Unit)))
((<) Num (Type.Id.uid (Type.Id.make Unit)))

// provably_equal takes two Id.t (last argument wrong)
(Type.Id.provably_equal Num)
(Type.Id.provably_equal Str)
(Type.Id.provably_equal true)
(Type.Id.provably_equal Unit)
(Type.Id.provably_equal (Option.some Num))
(Type.Id.provably_equal (Type.Id.make Unit) Num)
(Type.Id.provably_equal (Type.Id.make Unit) Str)
(Type.Id.provably_equal (Type.Id.make Unit) true)
(Type.Id.provably_equal (Type.Id.make Unit) Unit)
(Type.Id.provably_equal (Type.Id.make Unit) (Option.some Num))
(Type.Id.provably_equal (Type.Id.make Unit) (Option.some (Type.Id.make Unit)))

// provably_equal returns an option; what it holds is neither an Id.t nor a plain value
(Option.is_some (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit)))
(Option.get (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit)))
(Option.value (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit)) (Option.get (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit))))
((=) (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit)) (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit)))
((=) (Option.get (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit))) (Option.get (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit))))
((=) Num (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit)))
((=) Str (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit)))
((=) true (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit)))
((=) (Option.some Num) (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit)))
((=) (Option.some Str) (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit)))
((=) (Option.some (Type.Id.make Unit)) (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit)))
(succ (Option.get (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit))))
(not (Option.get (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit))))
((^) Str (Option.get (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit))))
(Type.Id.uid (Option.get (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit))))
(Option.value (Option.some Num) (Option.get (Type.Id.provably_equal (Type.Id.make Unit) (Type.Id.make Unit))))
