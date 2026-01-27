open Base
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
    hole_constraints = Hashtbl.create (module Int);
    insts = ref 0;
  }

let hole_equals t hole =
  if not t.evaluated then []
  else Hashtbl.find t.hole_constraints hole |> Option.value ~default:[]

let hole_equals_constructors t hole =
  hole_equals t hole
  |> List.filter_map ~f:(function
       | CArrow (l, r) -> Some (CArrow (l, r))
       | CLabel (lbl, ps) -> Some (CLabel (lbl, ps))
       | _ -> None)

let rec apply_binding ty v sub =
  match ty with
  | Bottom -> Bottom
  | CVar (v2, _) when Int.equal v2 v -> sub
  | CVar _ -> ty
  | CArrow (l, r) -> CArrow (apply_binding l v sub, apply_binding r v sub)
  | CLabel (lbl, ps) ->
      CLabel (lbl, List.map ps ~f:(fun p -> apply_binding p v sub))
  | Instantiation _ -> ty

let apply_bindings ty binds =
  List.fold binds ~init:ty ~f:(fun acc (v, sub) -> apply_binding acc v sub)

let rec unify param arg =
  match param with
  | Bottom -> Some []
  | CVar (v, _) ->
      if
        List.exists (constraint_variables arg) ~f:(fun (v2, _) -> Int.equal v v2)
      then None
      else Some [ (v, arg) ]
  | CArrow (lp, rp) -> (
      match arg with
      | Bottom -> Some []
      | CArrow (la, ra) ->
          let* b1 = unify lp la in
          let rp = apply_bindings rp b1 in
          let ra = apply_bindings ra b1 in
          let* b2 = unify rp ra in
          Some (b1 @ b2)
      | CVar (v2, _) -> Some [ (v2, param) ]
      | Instantiation _ -> None
      | CLabel _ -> None)
  | CLabel (lbl, ps) -> (
      match arg with
      | CLabel (lbl2, qs)
        when Int.equal lbl lbl2 && List.length ps = List.length qs ->
          let rec loop acc ps qs =
            match (ps, qs) with
            | [], [] -> Some acc
            | p :: ps', q :: qs' ->
                let* b = unify (apply_bindings p acc) (apply_bindings q acc) in
                loop (acc @ b) ps' qs'
            | _ -> None
          in
          loop [] ps qs
      | CVar (v2, _) -> Some [ (v2, param) ]
      | Bottom -> Some []
      | _ -> None)
  | Instantiation _ -> None

let hole_constraint inst ty =
  let key =
    match inst with
    | Instantiation (h, _) -> h
    | _ -> assert false
  in
  key, ty

let rec apply_fn fn arg =
  match fn with
  | CArrow (l, r) -> (
      match unify l arg with
      | None -> None
      | Some bindings -> Some (apply_bindings r bindings))
  | Instantiation _ as i -> Some (hole_constraint i arg |> snd)
  | _ -> None

let rec type_of t ex =
  match ex with
  | Example.Name name ->
      let inst = !(t.insts) in
      t.insts := inst + 1;
      instantiate inst (SearchState.type_of t.candidate name)
  | Example.App (f, a) -> (
      match type_of t f with
      | None -> None
      | Some fn -> (
          match type_of t a with
          | None -> None
          | Some arg -> apply_fn fn arg))

let ok t =
  if not t.evaluated then (
    t.error <- List.exists t.exs ~f:(fun ex -> Option.is_none (type_of t ex));
    t.evaluated <- true);
  not t.error
