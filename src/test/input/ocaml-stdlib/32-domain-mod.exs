// 0-basics.types, 1-comparison.types, 4-arith.types, 14-stdout.types, 16-stdin.types, 32-domain-mod.types

// spawn: (unit -> 'a) -> 'a t
(spawn print_newline)
(spawn read_line)
(spawn read_int)
(spawn flush_all)
(spawn (fun u1 -> print_newline u1))
(spawn (fun u2 -> read_line u2))

// join: 'a t -> 'a
(join (spawn print_newline))
(join (spawn read_line))
(join (spawn read_int))

// Predicates and counters
(is_main_domain Unit)
(recommended_domain_count Unit)
(self_index Unit)
(cpu_relax Unit)

// self: unit -> id
(self Unit)

// get_id: 'a t -> id
(get_id (spawn print_newline))
(get_id (spawn read_line))

// before_first_spawn and at_exit: (unit -> unit) -> unit
(before_first_spawn print_newline)
(before_first_spawn flush_all)
(at_exit print_newline)
(at_exit flush_all)

// Chaining: join extracts the value from the domain
(= (join (spawn read_line)) Str)
(= (join (spawn read_int)) Num)
(= (join (spawn is_main_domain)) true)
(succ (join (spawn read_int)))
(+ (join (spawn read_int)) Num)
(^ (join (spawn read_line)) Str)

// recommended_domain_count/self_index return int
(= (recommended_domain_count Unit) Num)
(= (self_index Unit) Num)
(succ (recommended_domain_count Unit))
(< (self_index Unit) (recommended_domain_count Unit))

// get_id / self return id: compare them
(= (self Unit) (self Unit))
(= (get_id (spawn print_newline)) (self Unit))

// is_main_domain returns bool
(= (is_main_domain Unit) true)

// DLS functions
(DLS.new_key print_newline)
(DLS.new_key read_line)
(DLS.get (DLS.new_key print_newline))
(DLS.get (DLS.new_key read_line))
(DLS.set (DLS.new_key read_line) Str)
(= (DLS.get (DLS.new_key read_line)) Str)
(^ (DLS.get (DLS.new_key read_line)) Str)

// Invalid
(join Num)
(spawn Num)
(get_id Num)
(before_first_spawn print_int)
(at_exit succ)
