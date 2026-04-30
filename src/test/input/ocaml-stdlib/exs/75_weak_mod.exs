// 0_basics.types, 1_comparison.types, 4_arith.types, 57_option_mod.types, 75_weak_mod.exs

// create: int -> 'a t
(create Num)

// length: 'a t -> int
(length (create Num))

// set: 'a t -> int -> 'a option -> unit
(set (create Num) Num (some Num))
(set (create Num) Num (some Str))
(set (create Num) Num none)

// get: 'a t -> int -> 'a option
(get (create Num) Num)

// get_copy: 'a t -> int -> 'a option
(get_copy (create Num) Num)

// check: 'a t -> int -> bool
(check (create Num) Num)

// fill: 'a t -> int -> int -> 'a option -> unit
(fill (create Num) Num Num (some Num))
(fill (create Num) Num Num none)

// blit: 'a t -> int -> 'a t -> int -> int -> unit
(blit (create Num) Num (create Num) Num Num)

// Chaining: create returns weak array — use length, check, get on it
(length (create Num))
(check (create Num) Num)
(get (create Num) Num)
(get_copy (create Num) Num)

// length returns int
(= (length (create Num)) Num)
(succ (length (create Num)))
(< (length (create Num)) Num)
(check (create Num) (length (create Num)))
(get (create Num) (length (create Num)))
(create (length (create Num)))

// check returns bool
(= (check (create Num) Num) true)
(not (check (create Num) Num))
(&& (check (create Num) Num) (check (create Num) Num))

// get/get_copy return 'a option — use is_some, is_none, get
(is_some (get (create Num) Num))
(is_none (get (create Num) Num))
(is_some (get_copy (create Num) Num))

// Invalid
(create Str)
(create true)
(length Num)
(check Num Num)
(check (create Num) Str)
(not (length (create Num)))
(succ (check (create Num) Num))
(get Num Num)
