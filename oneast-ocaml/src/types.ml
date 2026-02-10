open Stdlib
module IntMap = Map.Make (struct
  type t = int

  let compare = Stdlib.compare
end)

module StringMap = Map.Make (String)

module IntSet = Set.Make (struct
  type t = int

  let compare = Stdlib.compare
end)

type constraint_ty =
  | Bottom
  | Instantiation of int (* hole id *) * int (* inst id *)
  | CVar of int * int
  | CArrow of constraint_ty * constraint_ty
  | CLabel of int * constraint_ty list

let rec constraint_variables = function
  | Bottom -> []
  | Instantiation _ -> []
  | CVar (v, inst) -> [ (v, inst) ]
  | CArrow (l, r) -> constraint_variables l @ constraint_variables r
  | CLabel (_, ps) -> List.concat_map constraint_variables ps

module HoleId = struct
  let counter = ref 0
  let fresh () =
    let v = !counter in
    incr counter;
    v
  let reset () = counter := 0
end

type hole_kind = Blank of bool (* label_only *) | TypeHole

type hole = { id : int; kind : hole_kind }

type rec_type =
  | Variable of int
  | Arrow of rec_type * rec_type
  | NamedLabel of int * rec_type list
  | Hole of hole

type new_hole_kind = [ `Blank | `TypeHole ]

let make_hole ?(label_only = false) (kind : new_hole_kind) =
  let kind' = match kind with `Blank -> Blank label_only | `TypeHole -> TypeHole in
  Hole { id = HoleId.fresh (); kind = kind' }

let rec max_param_height ?(count_arrow = true) = function
  | Variable _ -> 1
  | Arrow (l, r) ->
      let left = max_param_height ~count_arrow:true l in
      let right = max_param_height ~count_arrow r in
      (if count_arrow then 1 else 0) + max left right
  | NamedLabel (_, ps) ->
      1
      + (match ps with
        | [] -> 0
        | _ ->
            List.fold_left
              (fun acc p -> max acc (max_param_height ~count_arrow p))
              0 ps)
  | Hole _ -> 1

let rec all_holes = function
  | Variable _ -> []
  | Arrow (l, r) -> all_holes l @ all_holes r
  | NamedLabel (_, ps) -> List.concat_map all_holes ps
  | Hole h -> [ h ]

let no_holes t = match all_holes t with [] -> true | _ -> false

let rec shallowest_fillable = function
  | Variable _ -> None
  | NamedLabel (_, ps) ->
      List.filter_map shallowest_fillable ps
      |> List.fold_left
           (fun acc elt ->
             match acc with
             | None -> Some elt
             | Some (_, d1) ->
                 let (_, d2) = elt in
                 if d2 < d1 then Some elt else acc)
           None
      |> Option.map (fun (h, d) -> (h, d + 1))
  | Arrow (l, r) -> (
      match (shallowest_fillable l, shallowest_fillable r) with
      | None, None -> None
      | Some (h, d), None | None, Some (h, d) -> Some (h, d + 1)
      | Some (_, d1), Some (h2, d2) ->
          if d1 <= d2 then Some (h2, d2 + 1) else Some (h2, d2 + 1))
  | Hole h -> (
      match h.kind with Blank _ -> None | TypeHole -> Some (h, 0))

let rec variables = function
  | Variable v -> IntSet.singleton v
  | Arrow (l, r) -> IntSet.union (variables l) (variables r)
  | NamedLabel (_, ps) ->
      List.fold_left
        (fun acc p -> IntSet.union acc (variables p))
        IntSet.empty ps
  | Hole _ -> IntSet.empty

let rec replace hole repl = function
  | Variable _ as v -> v
  | Arrow (l, r) -> Arrow (replace hole repl l, replace hole repl r)
  | NamedLabel (lbl, ps) -> NamedLabel (lbl, List.map (replace hole repl) ps)
  | Hole h as orig -> if h.id = hole.id then repl else orig

let rec instantiate inst_id = function
  | Variable v -> CVar (v, inst_id)
  | Arrow (l, r) -> CArrow (instantiate inst_id l, instantiate inst_id r)
  | NamedLabel (lbl, ps) -> CLabel (lbl, List.map (instantiate inst_id) ps)
  | Hole h -> Instantiation (h.id, inst_id)

let add_param_holes label_arities =
  let rec go ~under_arrow = function
    | Arrow (l, r) -> Arrow (go ~under_arrow:true l, go ~under_arrow:true r)
    | NamedLabel (lbl, ps) -> (
        match IntMap.find_opt lbl label_arities with
        | Some n when ps = [] && n > 0 ->
            let params =
            List.init n (fun _ ->
                  if under_arrow then make_hole `TypeHole
                  else make_hole ~label_only:false `Blank)
            in
            NamedLabel (lbl, params)
        | _ -> NamedLabel (lbl, List.map (go ~under_arrow) ps))
    | Hole _ as h -> h
    | Variable _ as v -> v
  in
  go ~under_arrow:false

module SearchState = struct
  type t = {
    names : int StringMap.t;
    types : rec_type list;
    rounds : int list;
    label_arities : int IntMap.t;
    id : int;
  }

  let next_id =
    let c = ref 0 in
    fun () ->
      let v = !c in
      incr c;
      v

  let empty =
    {
      names = StringMap.empty;
      types = [];
      rounds = [];
      label_arities = IntMap.empty;
      id = next_id ();
    }

  let create ?(names = StringMap.empty) ?(types = []) ?(rounds = [])
      ?(label_arities = IntMap.empty) () =
    { names; types; rounds; label_arities; id = next_id () }

  let map_types t ~f = { t with types = List.map f t.types }
  let map_types_i t ~f = { t with types = List.mapi f t.types }

  let map_types_set_arities t ~arities ~f =
    { t with types = List.map f t.types; label_arities = arities }

  let type_of t name =
    (* [names] indexes are assumed consistent with [types] *)
    let idx = StringMap.find name t.names in
    List.nth t.types idx

  let blanks t =
    List.concat_map
      (fun ty ->
        all_holes ty
        |> List.filter (fun h -> match h.kind with Blank _ -> true | _ -> false))
      t.types

  let no_fillable t =
    List.for_all (fun ty -> shallowest_fillable ty = None) t.types

  let no_holes t = List.for_all no_holes t.types

  let max_param_height t =
    List.fold_left
      (fun acc ty -> max acc (max_param_height ~count_arrow:false ty))
      0 t.types

  let fn_arities t =
    StringMap.map
      (fun idx ->
        let ty = List.nth t.types idx in
        let rec count acc = function
          | Arrow (_, r) -> count (acc + 1) r
          | _ -> acc
        in
        count 0 ty)
      t.names

  let as_map t = StringMap.map (fun idx -> List.nth t.types idx) t.names
end
