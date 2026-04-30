// 0_basics.types, 1_comparison.types, 4_arith.types, 14_stdout.types, 16_stdin.types, 32_domain_mod.types

// spawn: (unit -> 'a) -> 'a t
(Domain.spawn print_newline)
(Domain.spawn read_line)
(Domain.spawn read_int)
(Domain.spawn flush_all)
(Domain.spawn (fun u1 -> print_newline u1))
(Domain.spawn (fun u2 -> read_line u2))

// join: 'a t -> 'a
(Domain.join (Domain.spawn print_newline))
(Domain.join (Domain.spawn read_line))
(Domain.join (Domain.spawn read_int))

// Predicates and counters
(Domain.is_main_domain Unit)
(Domain.recommended_domain_count Unit)
(Domain.self_index Unit)
(Domain.cpu_relax Unit)

// self: unit -> id
(Domain.self Unit)

// get_id: 'a t -> id
(Domain.get_id (Domain.spawn print_newline))
(Domain.get_id (Domain.spawn read_line))

// before_first_spawn and at_exit: (unit -> unit) -> unit
(Domain.before_first_spawn print_newline)
(Domain.before_first_spawn flush_all)
(Domain.at_exit print_newline)
(Domain.at_exit flush_all)

// Chaining: join extracts the value from the domain
((=) (Domain.join (Domain.spawn read_line)) Str)
((=) (Domain.join (Domain.spawn read_int)) Num)
((=) (Domain.join (Domain.spawn Domain.is_main_domain)) true)
(succ (Domain.join (Domain.spawn read_int)))
((+) (Domain.join (Domain.spawn read_int)) Num)
((^) (Domain.join (Domain.spawn read_line)) Str)

// recommended_domain_count/self_index return int
((=) (Domain.recommended_domain_count Unit) Num)
((=) (Domain.self_index Unit) Num)
(succ (Domain.recommended_domain_count Unit))
((<) (Domain.self_index Unit) (Domain.recommended_domain_count Unit))

// get_id / self return id: compare them
((=) (Domain.self Unit) (Domain.self Unit))
((=) (Domain.get_id (Domain.spawn print_newline)) (Domain.self Unit))

// is_main_domain returns bool
((=) (Domain.is_main_domain Unit) true)

// DLS functions
(Domain.DLS.new_key print_newline)
(Domain.DLS.new_key read_line)
(Domain.DLS.get (Domain.DLS.new_key print_newline))
(Domain.DLS.get (Domain.DLS.new_key read_line))
(Domain.DLS.set (Domain.DLS.new_key read_line) Str)
((=) (Domain.DLS.get (Domain.DLS.new_key read_line)) Str)
((^) (Domain.DLS.get (Domain.DLS.new_key read_line)) Str)

// Invalid
(Domain.join Num)
(Domain.spawn Num)
(Domain.get_id Num)
(Domain.before_first_spawn print_int)
(Domain.at_exit succ)
