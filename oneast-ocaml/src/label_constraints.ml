open Base
open Types

let label_arities (s : SearchState.t) : (int, int, Int.comparator_witness) Map.t option =
  (* Placeholder: assume existing arities are final *)
  Some s.label_arities
