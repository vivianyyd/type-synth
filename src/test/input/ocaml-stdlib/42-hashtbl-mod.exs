// 0-basics.types, 1-comparison.types, 4-arith.types, 7-str.types, 9-unit.types, 14-stdout.types, 42-hashtbl-mod.types

// Construction
(create Num)

// add: ('a,'b) t -> 'a -> 'b -> unit
(add (create Num) Num Str)
(add (create Num) Str Num)
(add (create Num) Num Num)
(add (create Num) Str Str)
(add (create Num) true Num)
(add (create Num) Num true)

// find: ('a,'b) t -> 'a -> 'b
(find (create Num) Num)
(find (create Num) Str)

// find_opt: ('a,'b) t -> 'a -> 'b option
(find_opt (create Num) Num)
(find_opt (create Num) Str)

// find_all: ('a,'b) t -> 'a -> 'b list
(find_all (create Num) Num)
(find_all (create Num) Str)

// mem: ('a,'b) t -> 'a -> bool
(mem (create Num) Num)
(mem (create Num) Str)
(mem (create Num) true)

// remove, replace: unit
(remove (create Num) Num)
(replace (create Num) Num Str)
(replace (create Num) Str Num)

// copy, clear, reset
(copy (create Num))
(clear (create Num))
(reset (create Num))

// length: int
(length (create Num))
(length (copy (create Num)))

// is_randomized, randomize
(is_randomized Unit)
(randomize Unit)

// rebuild: ('a,'b) t -> ('a,'b) t
(rebuild (create Num))

// iter: ('a -> 'b -> unit) -> ('a,'b) t -> unit
(iter (fun k1 v1 -> ignore k1) (create Num))
(iter (fun k2 v2 -> print_int v2) (create Num))

// fold: ('a -> 'b -> 'acc -> 'acc) -> ('a,'b) t -> 'acc -> 'acc
(fold (fun k3 v3 acc -> acc) (create Num) Num)
(fold (fun k4 v4 acc -> (+ acc v4)) (create Num) Num)

// hash, seeded_hash, hash_param, seeded_hash_param: polymorphic, return int
(hash Num)
(hash Str)
(hash true)
(seeded_hash Num Str)
(seeded_hash Num true)
(hash_param Num Num Str)
(seeded_hash_param Num Num Num Str)

// Chaining: length returns int
(= (length (create Num)) Num)
(succ (length (create Num)))
(< (length (create Num)) Num)
(length (copy (create Num)))
(= (length (copy (create Num))) Num)
(= (length (rebuild (create Num))) Num)

// mem returns bool
(= (mem (create Num) Num) true)
(not (mem (create Num) Num))
(= (mem (create Num) Num) (mem (create Num) Str))

// hash returns int: use in arithmetic and as table key
(= (hash Num) Num)
(succ (hash Str))
(+ (hash Num) (hash Str))
(add (create Num) (hash Num) Str)
(add (create Num) (hash Str) Num)
(mem (create Num) (hash Num))

// seeded_hash returns int
(= (seeded_hash Num Str) Num)
(succ (seeded_hash Num true))
(+ (seeded_hash Num Str) (hash Num))
(add (create Num) (seeded_hash Num Str) Num)

// copy/rebuild return same table type
(length (copy (create Num)))
(mem (copy (create Num)) Num)
(length (rebuild (create Num)))

// is_randomized returns bool
(= (is_randomized Unit) true)
(not (is_randomized Unit))

// fold result used further
(succ (fold (fun k5 v5 acc -> (+ acc Num)) (create Num) Num))
(= (fold (fun k6 v6 acc -> acc) (create Num) Num) Num)

// Invalid: wrong types used with hash / length outputs
(^ (hash Num) Str)
(not (hash Num))
(find (length (create Num)) Num)
(add (create Num) Num (length (create Num)))
(mem (create Num) (mem (create Num) Num))
(succ (mem (create Num) Num))
(add (length (create Num)) Num Str)
