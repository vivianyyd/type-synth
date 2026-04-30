// 0_basics.types, 1_comparison.types, 4_arith.types, 49_lexing_mod.types, 59_parsing_mod.types

// symbol_start, symbol_end: unit -> int
(symbol_start Unit)
(symbol_end Unit)

// rhs_start, rhs_end: int -> int
(rhs_start Num)
(rhs_end Num)

// symbol_start_pos, symbol_end_pos: unit -> position
(symbol_start_pos Unit)
(symbol_end_pos Unit)

// rhs_start_pos, rhs_end_pos: int -> position
(rhs_start_pos Num)
(rhs_end_pos Num)

// clear_parser: unit -> unit
(clear_parser Unit)

// set_trace: bool -> bool
(set_trace true)
(set_trace false)

// Chaining: symbol_start/symbol_end return int — use in arithmetic and as rhs_start/rhs_end arguments
(= (symbol_start Unit) Num)
(= (symbol_end Unit) Num)
(< (symbol_start Unit) (symbol_end Unit))
(succ (symbol_start Unit))
(pred (symbol_end Unit))
(- (symbol_end Unit) (symbol_start Unit))
(rhs_start (symbol_start Unit))
(rhs_end (symbol_end Unit))
(rhs_start_pos (symbol_start Unit))
(rhs_end_pos (symbol_end Unit))

// rhs_start/rhs_end return int — chain into more ops
(= (rhs_start Num) Num)
(= (rhs_end Num) Num)
(< (rhs_start Num) (rhs_end Num))
(succ (rhs_start Num))
(rhs_end (rhs_start Num))
(rhs_start_pos (rhs_end Num))
(- (rhs_end Num) (rhs_start Num))

// set_trace returns bool — use in bool ops or comparisons
(= (set_trace true) true)
(= (set_trace false) false)
(not (set_trace false))
(&& (set_trace true) (set_trace true))
(set_trace (set_trace true))

// rhs_start_pos/rhs_end_pos return position — use in lexing position ops
(= (rhs_start_pos Num) (symbol_start_pos Unit))
(= (rhs_end_pos Num) (symbol_end_pos Unit))

// Invalid
(succ (set_trace true))
(not (symbol_start Unit))
(rhs_start Str)
(rhs_end true)
(rhs_start_pos Str)
(symbol_start Num)
(set_trace Num)
