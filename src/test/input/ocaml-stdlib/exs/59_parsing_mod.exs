// 0_basics.types, 1_comparison.types, 4_arith.types, 49_lexing_mod.types, 59_parsing_mod.types

// symbol_start, symbol_end: unit -> int
(Parsing.symbol_start Unit)
(Parsing.symbol_end Unit)

// rhs_start, rhs_end: int -> int
(Parsing.rhs_start Num)
(Parsing.rhs_end Num)

// symbol_start_pos, symbol_end_pos: unit -> position
(Parsing.symbol_start_pos Unit)
(Parsing.symbol_end_pos Unit)

// rhs_start_pos, rhs_end_pos: int -> position
(Parsing.rhs_start_pos Num)
(Parsing.rhs_end_pos Num)

// clear_parser: unit -> unit
(Parsing.clear_parser Unit)

// set_trace: bool -> bool
(Parsing.set_trace true)
(Parsing.set_trace false)

// Chaining: symbol_start/symbol_end return int — use in arithmetic and as rhs_start/rhs_end arguments
((=) (Parsing.symbol_start Unit) Num)
((=) (Parsing.symbol_end Unit) Num)
((<) (Parsing.symbol_start Unit) (Parsing.symbol_end Unit))
(succ (Parsing.symbol_start Unit))
(pred (Parsing.symbol_end Unit))
((-) (Parsing.symbol_end Unit) (Parsing.symbol_start Unit))
(Parsing.rhs_start (Parsing.symbol_start Unit))
(Parsing.rhs_end (Parsing.symbol_end Unit))
(Parsing.rhs_start_pos (Parsing.symbol_start Unit))
(Parsing.rhs_end_pos (Parsing.symbol_end Unit))

// rhs_start/rhs_end return int — chain into more ops
((=) (Parsing.rhs_start Num) Num)
((=) (Parsing.rhs_end Num) Num)
((<) (Parsing.rhs_start Num) (Parsing.rhs_end Num))
(succ (Parsing.rhs_start Num))
(Parsing.rhs_end (Parsing.rhs_start Num))
(Parsing.rhs_start_pos (Parsing.rhs_end Num))
((-) (Parsing.rhs_end Num) (Parsing.rhs_start Num))

// set_trace returns bool — use in bool ops or comparisons
((=) (Parsing.set_trace true) true)
((=) (Parsing.set_trace false) false)
(not (Parsing.set_trace false))
((&&) (Parsing.set_trace true) (Parsing.set_trace true))
(Parsing.set_trace (Parsing.set_trace true))

// rhs_start_pos/rhs_end_pos return position — use in lexing position ops
((=) (Parsing.rhs_start_pos Num) (Parsing.symbol_start_pos Unit))
((=) (Parsing.rhs_end_pos Num) (Parsing.symbol_end_pos Unit))

// Invalid
(succ (Parsing.set_trace true))
(not (Parsing.symbol_start Unit))
(Parsing.rhs_start Str)
(Parsing.rhs_end true)
(Parsing.rhs_start_pos Str)
(Parsing.symbol_start Num)
(Parsing.set_trace Num)
