// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 9_unit.types, 14_stdout.types, 42_hashtbl_mod.types

// Construction
(Hashtbl.create Num)

// add: ('a,'b) t -> 'a -> 'b -> unit
(Hashtbl.add (Hashtbl.create Num) Num Str)
(Hashtbl.add (Hashtbl.create Num) Str Num)
(Hashtbl.add (Hashtbl.create Num) Num Num)
(Hashtbl.add (Hashtbl.create Num) Str Str)
(Hashtbl.add (Hashtbl.create Num) true Num)
(Hashtbl.add (Hashtbl.create Num) Num true)

// find: ('a,'b) t -> 'a -> 'b
(Hashtbl.find (Hashtbl.create Num) Num)
(Hashtbl.find (Hashtbl.create Num) Str)

// find_opt: ('a,'b) t -> 'a -> 'b option
(Hashtbl.find_opt (Hashtbl.create Num) Num)
(Hashtbl.find_opt (Hashtbl.create Num) Str)

// find_all: ('a,'b) t -> 'a -> 'b list
(Hashtbl.find_all (Hashtbl.create Num) Num)
(Hashtbl.find_all (Hashtbl.create Num) Str)

// mem: ('a,'b) t -> 'a -> bool
(Hashtbl.mem (Hashtbl.create Num) Num)
(Hashtbl.mem (Hashtbl.create Num) Str)
(Hashtbl.mem (Hashtbl.create Num) true)

// remove, replace: unit
(Hashtbl.remove (Hashtbl.create Num) Num)
(Hashtbl.replace (Hashtbl.create Num) Num Str)
(Hashtbl.replace (Hashtbl.create Num) Str Num)

// copy, clear, reset
(Hashtbl.copy (Hashtbl.create Num))
(Hashtbl.clear (Hashtbl.create Num))
(Hashtbl.reset (Hashtbl.create Num))

// length: int
(Hashtbl.length (Hashtbl.create Num))
(Hashtbl.length (Hashtbl.copy (Hashtbl.create Num)))

// is_randomized, randomize
(Hashtbl.is_randomized Unit)
(Hashtbl.randomize Unit)

// rebuild: ('a,'b) t -> ('a,'b) t
(Hashtbl.rebuild (Hashtbl.create Num))

// iter: ('a -> 'b -> unit) -> ('a,'b) t -> unit
(Hashtbl.iter (fun k1 v1 -> ignore k1) (Hashtbl.create Num))
(Hashtbl.iter (fun k2 v2 -> print_int v2) (Hashtbl.create Num))

// fold: ('a -> 'b -> 'acc -> 'acc) -> ('a,'b) t -> 'acc -> 'acc
(Hashtbl.fold (fun k3 v3 acc -> acc) (Hashtbl.create Num) Num)
(Hashtbl.fold (fun k4 v4 acc -> ((+) acc v4)) (Hashtbl.create Num) Num)

// hash, seeded_hash, hash_param, seeded_hash_param: polymorphic, return int
(Hashtbl.hash Num)
(Hashtbl.hash Str)
(Hashtbl.hash true)
(Hashtbl.seeded_hash Num Str)
(Hashtbl.seeded_hash Num true)
(Hashtbl.hash_param Num Num Str)
(Hashtbl.seeded_hash_param Num Num Num Str)

// Chaining: length returns int
((=) (Hashtbl.length (Hashtbl.create Num)) Num)
(succ (Hashtbl.length (Hashtbl.create Num)))
((<) (Hashtbl.length (Hashtbl.create Num)) Num)
(Hashtbl.length (Hashtbl.copy (Hashtbl.create Num)))
((=) (Hashtbl.length (Hashtbl.copy (Hashtbl.create Num))) Num)
((=) (Hashtbl.length (Hashtbl.rebuild (Hashtbl.create Num))) Num)

// mem returns bool
((=) (Hashtbl.mem (Hashtbl.create Num) Num) true)
(not (Hashtbl.mem (Hashtbl.create Num) Num))
((=) (Hashtbl.mem (Hashtbl.create Num) Num) (Hashtbl.mem (Hashtbl.create Num) Str))

// hash returns int: use in arithmetic and as table key
((=) (Hashtbl.hash Num) Num)
(succ (Hashtbl.hash Str))
((+) (Hashtbl.hash Num) (Hashtbl.hash Str))
(Hashtbl.add (Hashtbl.create Num) (Hashtbl.hash Num) Str)
(Hashtbl.add (Hashtbl.create Num) (Hashtbl.hash Str) Num)
(Hashtbl.mem (Hashtbl.create Num) (Hashtbl.hash Num))

// seeded_hash returns int
((=) (Hashtbl.seeded_hash Num Str) Num)
(succ (Hashtbl.seeded_hash Num true))
((+) (Hashtbl.seeded_hash Num Str) (Hashtbl.hash Num))
(Hashtbl.add (Hashtbl.create Num) (Hashtbl.seeded_hash Num Str) Num)

// copy/rebuild return same table type
(Hashtbl.length (Hashtbl.copy (Hashtbl.create Num)))
(Hashtbl.mem (Hashtbl.copy (Hashtbl.create Num)) Num)
(Hashtbl.length (Hashtbl.rebuild (Hashtbl.create Num)))

// is_randomized returns bool
((=) (Hashtbl.is_randomized Unit) true)
(not (Hashtbl.is_randomized Unit))

// fold result used further
(succ (Hashtbl.fold (fun k5 v5 acc -> ((+) acc Num)) (Hashtbl.create Num) Num))
((=) (Hashtbl.fold (fun k6 v6 acc -> acc) (Hashtbl.create Num) Num) Num)

// Invalid: wrong types used with hash / length outputs
((^) (Hashtbl.hash Num) Str)
(not (Hashtbl.hash Num))
(Hashtbl.find (Hashtbl.length (Hashtbl.create Num)) Num)
(Hashtbl.add (Hashtbl.create Num) Num (Hashtbl.length (Hashtbl.create Num)))
(Hashtbl.mem (Hashtbl.create Num) (Hashtbl.mem (Hashtbl.create Num) Num))
(succ (Hashtbl.mem (Hashtbl.create Num) Num))
(Hashtbl.add (Hashtbl.length (Hashtbl.create Num)) Num Str)
