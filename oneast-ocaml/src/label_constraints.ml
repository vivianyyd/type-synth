open Base
open Types

(* Placeholder: real solver not implemented; we model by echoing existing arities *)

let solve_label_arities (_state : SearchState.t) (_deps : unit) =
  Some _state.SearchState.label_arities
