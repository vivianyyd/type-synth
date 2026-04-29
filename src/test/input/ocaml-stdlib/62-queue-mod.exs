// 0-basics.types, 1-comparison.types, 4-arith.types, 7-str.types, 9-unit.types, 10-strconv.types, 14-stdout.types, 62-queue-mod.types

// create: unit -> 'a t
(create Unit)

// add, push: 'a -> 'a t -> unit
(add Num (create Unit))
(add Str (create Unit))
(push Num (create Unit))
(push Str (create Unit))

// take, pop, peek, top: 'a t -> 'a
(take (create Unit))
(pop (create Unit))
(peek (create Unit))
(top (create Unit))

// take_opt, peek_opt: 'a t -> 'a option
(take_opt (create Unit))
(peek_opt (create Unit))

// drop, clear: 'a t -> unit
(drop (create Unit))
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

// transfer: 'a t -> 'a t -> unit
(transfer (create Unit) (create Unit))

// Chaining: length returns int
(= (length (create Unit)) Num)
(< (length (create Unit)) Num)
(succ (length (create Unit)))
(= (length (copy (create Unit))) (length (create Unit)))

// is_empty returns bool
(= (is_empty (create Unit)) true)
(not (is_empty (create Unit)))
(&& (is_empty (create Unit)) (is_empty (create Unit)))

// copy returns queue — use length, is_empty on it
(length (copy (create Unit)))
(is_empty (copy (create Unit)))
(take (copy (create Unit)))
(drop (copy (create Unit)))

// fold returns accumulator type
(= (fold (+) Num (create Unit)) Num)
(succ (fold (+) Num (create Unit)))
(< (fold (+) Num (create Unit)) Num)
(fold (+) (fold (+) Num (create Unit)) (create Unit))

// take/pop/peek/top return element type
(= (take (create Unit)) Num)
(succ (take (create Unit)))
(add (take (copy (create Unit))) (create Unit))
(= (peek (create Unit)) (top (create Unit)))

// Invalid
(succ (is_empty (create Unit)))
(not (length (create Unit)))
(add Num (length (create Unit)))
(length Num)
(is_empty Num)
(take Num)
(fold (+) Str (create Unit))
