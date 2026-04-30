// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 9_unit.types, 10_strconv.types, 14_stdout.types, 62_queue_mod.types

// create: unit -> 'a t
(Queue.create Unit)

// add, push: 'a -> 'a t -> unit
(Queue.add Num (Queue.create Unit))
(Queue.add Str (Queue.create Unit))
(Queue.push Num (Queue.create Unit))
(Queue.push Str (Queue.create Unit))

// take, pop, peek, top: 'a t -> 'a
(Queue.take (Queue.create Unit))
(Queue.pop (Queue.create Unit))
(Queue.peek (Queue.create Unit))
(Queue.top (Queue.create Unit))

// take_opt, peek_opt: 'a t -> 'a option
(Queue.take_opt (Queue.create Unit))
(Queue.peek_opt (Queue.create Unit))

// drop, clear: 'a t -> unit
(Queue.drop (Queue.create Unit))
(Queue.clear (Queue.create Unit))

// copy: 'a t -> 'a t
(Queue.copy (Queue.create Unit))

// is_empty: 'a t -> bool
(Queue.is_empty (Queue.create Unit))

// length: 'a t -> int
(Queue.length (Queue.create Unit))

// iter: ('a -> unit) -> 'a t -> unit
(Queue.iter ignore (Queue.create Unit))
(Queue.iter print_int (Queue.create Unit))
(Queue.iter print_string (Queue.create Unit))

// fold: ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
(Queue.fold (+) Num (Queue.create Unit))
(Queue.fold (^) Str (Queue.create Unit))

// transfer: 'a t -> 'a t -> unit
(Queue.transfer (Queue.create Unit) (Queue.create Unit))

// Chaining: length returns int
((=) (Queue.length (Queue.create Unit)) Num)
((<) (Queue.length (Queue.create Unit)) Num)
(succ (Queue.length (Queue.create Unit)))
((=) (Queue.length (Queue.copy (Queue.create Unit))) (Queue.length (Queue.create Unit)))

// is_empty returns bool
((=) (Queue.is_empty (Queue.create Unit)) true)
(not (Queue.is_empty (Queue.create Unit)))
((&&) (Queue.is_empty (Queue.create Unit)) (Queue.is_empty (Queue.create Unit)))

// copy returns queue — use length, is_empty on it
(Queue.length (Queue.copy (Queue.create Unit)))
(Queue.is_empty (Queue.copy (Queue.create Unit)))
(Queue.take (Queue.copy (Queue.create Unit)))
(Queue.drop (Queue.copy (Queue.create Unit)))

// fold returns accumulator type
((=) (Queue.fold (+) Num (Queue.create Unit)) Num)
(succ (Queue.fold (+) Num (Queue.create Unit)))
((<) (Queue.fold (+) Num (Queue.create Unit)) Num)
(Queue.fold (+) (Queue.fold (+) Num (Queue.create Unit)) (Queue.create Unit))

// take/pop/peek/top return element type
((=) (Queue.take (Queue.create Unit)) Num)
(succ (Queue.take (Queue.create Unit)))
(Queue.add (Queue.take (Queue.copy (Queue.create Unit))) (Queue.create Unit))
((=) (Queue.peek (Queue.create Unit)) (Queue.top (Queue.create Unit)))

// Invalid
(succ (Queue.is_empty (Queue.create Unit)))
(not (Queue.length (Queue.create Unit)))
(Queue.add Num (Queue.length (Queue.create Unit)))
(Queue.length Num)
(Queue.is_empty Num)
(Queue.take Num)
(Queue.fold (+) Str (Queue.create Unit))
