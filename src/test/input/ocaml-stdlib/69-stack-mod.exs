// 0-basics.types, 1-comparison.types, 4-arith.types, 7-str.types, 9-unit.types, 14-stdout.types, 69-stack-mod.types

// create: unit -> 'a t
(create Unit)

// push: 'a -> 'a t -> unit
(push Num (create Unit))
(push Str (create Unit))
(push true (create Unit))

// pop: 'a t -> 'a
(pop (create Unit))

// pop_opt: 'a t -> 'a option
(pop_opt (create Unit))

// drop: 'a t -> unit
(drop (create Unit))

// top: 'a t -> 'a
(top (create Unit))

// top_opt: 'a t -> 'a option
(top_opt (create Unit))

// clear: 'a t -> unit
(clear (create Unit))

// copy: 'a t -> 'a t
(copy (create Unit))

// is_empty: 'a t -> bool
(is_empty (create Unit))

// length: 'a t -> int
(length (create Unit))

// iter: ('a -> unit) -> 'a t -> unit
(iter ignore (create Unit))
(iter print_int (create Unit))
(iter print_string (create Unit))

// fold: ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
(fold (+) Num (create Unit))
(fold (^) Str (create Unit))

// Chaining: copy returns stack — use same ops
(length (copy (create Unit)))
(is_empty (copy (create Unit)))
(top (copy (create Unit)))
(pop (copy (create Unit)))

// length returns int
(= (length (create Unit)) Num)
(succ (length (create Unit)))
(< (length (create Unit)) Num)
(= (length (copy (create Unit))) (length (create Unit)))

// is_empty returns bool
(= (is_empty (create Unit)) true)
(not (is_empty (create Unit)))
(&& (is_empty (create Unit)) (is_empty (create Unit)))

// pop/top return element type
(= (pop (create Unit)) Num)
(succ (pop (create Unit)))
(push (pop (copy (create Unit))) (create Unit))
(= (top (create Unit)) (pop (create Unit)))

// fold returns accumulator
(= (fold (+) Num (create Unit)) Num)
(succ (fold (+) Num (create Unit)))
(< (fold (+) Num (create Unit)) Num)
(fold (+) (fold (+) Num (create Unit)) (create Unit))

// Invalid
(succ (is_empty (create Unit)))
(not (length (create Unit)))
(push Num (length (create Unit)))
(length Num)
(is_empty Str)
(pop Num)
(fold (+) Str (create Unit))
