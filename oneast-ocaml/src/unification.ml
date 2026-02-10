open Types

type binding = constraint_ty * constraint_ty

type t = {
  candidate : SearchState.t;
  exs : Example.t list;
  mutable evaluated : bool;
  mutable error : bool;
  hole_constraints : (int, constraint_ty list) Hashtbl.t;
  insts : int ref;
}

let create candidate exs =
  {
    candidate;
    exs;
    evaluated = false;
    error = false;
    hole_constraints = Hashtbl.create 16;
    insts = ref 0;
  }

let hole_equals t hole =
  if not t.evaluated then []
  else Hashtbl.find_opt t.hole_constraints hole |> Option.value ~default:[]

let hole_equals_constructors t hole =
  hole_equals t hole
  |> List.filter_map (function
         | CArrow (l, r) -> Some (CArrow (l, r))
         | CLabel (lbl, ps) -> Some (CLabel (lbl, ps))
         | _ -> None)

let rec apply_binding ty v sub =
  match ty with
  | Bottom -> Bottom
  | CVar (v2, _) when v2 = v -> sub
  | CVar _ -> ty
  | CArrow (l, r) -> CArrow (apply_binding l v sub, apply_binding r v sub)
  | CLabel (lbl, ps) ->
      CLabel (lbl, List.map (fun p -> apply_binding p v sub) ps)
  | Instantiation _ -> ty

let apply_bindings ty binds =
  List.fold_left (fun acc (v, sub) -> apply_binding acc v sub) ty binds

let rec unify param arg =
  match param with
  | Bottom -> Some []
  | CVar (v, _) ->
      if List.exists (fun (v2, _) -> v = v2) (constraint_variables arg) then None
      else Some [ (v, arg) ]
  | CArrow (lp, rp) -> (
      match arg with
      | Bottom -> Some []
      | CArrow (la, ra) -> (
          match unify lp la with
          | None -> None
          | Some b1 -> (
              match unify (apply_bindings rp b1) (apply_bindings ra b1) with
              | None -> None
              | Some b2 -> Some (b1 @ b2)))
      | CVar (v2, _) -> Some [ (v2, param) ]
      | Instantiation _ -> None
      | CLabel _ -> None)
  | CLabel (lbl, ps) -> (
      match arg with
      | CLabel (lbl2, qs)
        when lbl = lbl2 && List.length ps = List.length qs ->
          let rec loop acc ps qs =
            match (ps, qs) with
            | [], [] -> Some acc
            | p :: ps', q :: qs' -> (
                match unify (apply_bindings p acc) (apply_bindings q acc) with
                | None -> None
                | Some b -> loop (acc @ b) ps' qs')
            | _ -> None
          in
          loop [] ps qs
      | CVar (v2, _) -> Some [ (v2, param) ]
      | Bottom -> Some []
      | _ -> None)
  | Instantiation _ -> None

let hole_constraint inst ty =
  match inst with
  | Instantiation (h, _) -> (h, ty)
  | _ -> assert false

let apply_fn fn arg =
  match fn with
  | CArrow (l, r) -> (
      match unify l arg with
      | None -> None
      | Some bindings -> Some (apply_bindings r bindings))
  | Instantiation _ as i -> Some (snd (hole_constraint i arg))
  | _ -> None

let rec type_of t ex =
  match ex with
  | Example.Name name ->
      let inst = !(t.insts) in
      t.insts := inst + 1;
      Some (instantiate inst (SearchState.type_of t.candidate name))
  | Example.App (f, a) -> (
      match type_of t f with
      | None -> None
      | Some fn -> (
          match type_of t a with
          | None -> None
          | Some arg -> apply_fn fn arg))

let ok t =
  if not t.evaluated then (
    t.error <- List.exists (fun ex -> type_of t ex = None) t.exs;
    t.evaluated <- true);
  not t.error
