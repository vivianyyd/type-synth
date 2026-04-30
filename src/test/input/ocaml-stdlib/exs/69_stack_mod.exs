// 0_basics.types, 1_comparison.types, 4_arith.types, 7_str.types, 9_unit.types, 14_stdout.types, 69_stack_mod.types

// create: unit -> 'a t
(Stack.create Unit)

// push: 'a -> 'a t -> unit
(Stack.push Num (Stack.create Unit))
(Stack.push Str (Stack.create Unit))
(Stack.push true (Stack.create Unit))

// pop: 'a t -> 'a
(Stack.pop (Stack.create Unit))

// pop_opt: 'a t -> 'a option
(Stack.pop_opt (Stack.create Unit))

// drop: 'a t -> unit
(Stack.drop (Stack.create Unit))

// top: 'a t -> 'a
(Stack.top (Stack.create Unit))

// top_opt: 'a t -> 'a option
(Stack.top_opt (Stack.create Unit))

// clear: 'a t -> unit
(Stack.clear (Stack.create Unit))

// copy: 'a t -> 'a t
(Stack.copy (Stack.create Unit))

// is_empty: 'a t -> bool
(Stack.is_empty (Stack.create Unit))

// length: 'a t -> int
(Stack.length (Stack.create Unit))

// iter: ('a -> unit) -> 'a t -> unit
(Stack.iter ignore (Stack.create Unit))
(Stack.iter print_int (Stack.create Unit))
(Stack.iter print_string (Stack.create Unit))

// fold: ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
(Stack.fold (+) Num (Stack.create Unit))
(Stack.fold (^) Str (Stack.create Unit))

// Chaining: copy returns stack — use same ops
(Stack.length (Stack.copy (Stack.create Unit)))
(Stack.is_empty (Stack.copy (Stack.create Unit)))
(Stack.top (Stack.copy (Stack.create Unit)))
(Stack.pop (Stack.copy (Stack.create Unit)))

// length returns int
((=) (Stack.length (Stack.create Unit)) Num)
(succ (Stack.length (Stack.create Unit)))
((<) (Stack.length (Stack.create Unit)) Num)
((=) (Stack.length (Stack.copy (Stack.create Unit))) (Stack.length (Stack.create Unit)))

// is_empty returns bool
((=) (Stack.is_empty (Stack.create Unit)) true)
(not (Stack.is_empty (Stack.create Unit)))
((&&) (Stack.is_empty (Stack.create Unit)) (Stack.is_empty (Stack.create Unit)))

// pop/top return element type
((=) (Stack.pop (Stack.create Unit)) Num)
(succ (Stack.pop (Stack.create Unit)))
(Stack.push (Stack.pop (Stack.copy (Stack.create Unit))) (Stack.create Unit))
((=) (Stack.top (Stack.create Unit)) (Stack.pop (Stack.create Unit)))

// fold returns accumulator
((=) (Stack.fold (+) Num (Stack.create Unit)) Num)
(succ (Stack.fold (+) Num (Stack.create Unit)))
((<) (Stack.fold (+) Num (Stack.create Unit)) Num)
(Stack.fold (+) (Stack.fold (+) Num (Stack.create Unit)) (Stack.create Unit))

// Invalid
(succ (Stack.is_empty (Stack.create Unit)))
(not (Stack.length (Stack.create Unit)))
(Stack.push Num (Stack.length (Stack.create Unit)))
(Stack.length Num)
(Stack.is_empty Str)
(Stack.pop Num)
(Stack.fold (+) Str (Stack.create Unit))
