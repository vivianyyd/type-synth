// 0_basics.types, 1_comparison.types, 4_arith.types, 57_option_mod.types, 75_weak_mod.exs

// create: int -> 'a t
(Weak.create Num)

// length: 'a t -> int
(Weak.length (Weak.create Num))

// set: 'a t -> int -> 'a option -> unit
(Weak.set (Weak.create Num) Num (Option.some Num))
(Weak.set (Weak.create Num) Num (Option.some Str))
(Weak.set (Weak.create Num) Num Option.none)

// get: 'a t -> int -> 'a option
(Weak.get (Weak.create Num) Num)

// get_copy: 'a t -> int -> 'a option
(Weak.get_copy (Weak.create Num) Num)

// check: 'a t -> int -> bool
(Weak.check (Weak.create Num) Num)

// fill: 'a t -> int -> int -> 'a option -> unit
(Weak.fill (Weak.create Num) Num Num (Option.some Num))
(Weak.fill (Weak.create Num) Num Num Option.none)

// blit: 'a t -> int -> 'a t -> int -> int -> unit
(Weak.blit (Weak.create Num) Num (Weak.create Num) Num Num)

// Chaining: create returns weak array — use length, check, get on it
(Weak.length (Weak.create Num))
(Weak.check (Weak.create Num) Num)
(Weak.get (Weak.create Num) Num)
(Weak.get_copy (Weak.create Num) Num)

// length returns int
((=) (Weak.length (Weak.create Num)) Num)
(succ (Weak.length (Weak.create Num)))
((<) (Weak.length (Weak.create Num)) Num)
(Weak.check (Weak.create Num) (Weak.length (Weak.create Num)))
(Weak.get (Weak.create Num) (Weak.length (Weak.create Num)))
(Weak.create (Weak.length (Weak.create Num)))

// check returns bool
((=) (Weak.check (Weak.create Num) Num) true)
(not (Weak.check (Weak.create Num) Num))
((&&) (Weak.check (Weak.create Num) Num) (Weak.check (Weak.create Num) Num))

// get/get_copy return 'a option — use is_some, is_none, get
(Option.is_some (Weak.get (Weak.create Num) Num))
(Option.is_none (Weak.get (Weak.create Num) Num))
(Option.is_some (Weak.get_copy (Weak.create Num) Num))

// Invalid
(Weak.create Str)
(Weak.create true)
(Weak.length Num)
(Weak.check Num Num)
(Weak.check (Weak.create Num) Str)
(not (Weak.length (Weak.create Num)))
(succ (Weak.check (Weak.create Num) Num))
(Weak.get Num Num)
