open Base

type constraint_ty =
  | Bottom
  | Instantiation of int (* hole id *) * int (* inst id *)
  | CVar of int * int
  | CArrow of constraint_ty * constraint_ty
  | CLabel of int * constraint_ty list

let constraint_variables = function
  | Bottom -> []
  | Instantiation _ -> []
  | CVar (v, inst) -> [ (v, inst) ]
  | CArrow (l, r) -> constraint_variables l @ constraint_variables r
  | CLabel (_, ps) -> List.concat_map ps ~f:constraint_variables

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
      (if count_arrow then 1 else 0)
      + Int.max (max_param_height ~count_arrow:true l)
          (max_param_height ~count_arrow r)
  | NamedLabel (_, ps) ->
      1
      + Option.value ~default:0
          (List.max_elt ~compare:Int.compare
             (List.map ps ~f:(max_param_height ~count_arrow)))
  | Hole _ -> 1

let rec all_holes = function
  | Variable _ -> []
  | Arrow (l, r) -> all_holes l @ all_holes r
  | NamedLabel (_, ps) -> List.concat_map ps ~f:all_holes
  | Hole h -> [ h ]

let no_holes t = List.is_empty (all_holes t)

let rec shallowest_fillable = function
  | Variable _ -> None
  | NamedLabel (_, ps) ->
      List.filter_map ps ~f:shallowest_fillable
      |> List.min_elt ~compare:(fun (_, d1) (_, d2) -> Int.compare d1 d2)
      |> Option.map ~f:(fun (h, d) -> (h, d + 1))
  | Arrow (l, r) -> (
      match (shallowest_fillable l, shallowest_fillable r) with
      | None, None -> None
      | Some (h, d), None | None, Some (h, d) -> Some (h, d + 1)
      | Some (_, d1), Some (h2, d2) ->
          if d1 <= d2 then Some (h2, d2 + 1) else Some (h2, d2 + 1))
  | Hole h -> (
      match h.kind with Blank _ -> None | TypeHole -> Some (h, 0))

let rec variables = function
  | Variable v -> Set.singleton (module Int) v
  | Arrow (l, r) -> Set.union (variables l) (variables r)
  | NamedLabel (_, ps) ->
      List.fold ps ~init:(Set.empty (module Int)) ~f:(fun acc p ->
          Set.union acc (variables p))
  | Hole _ -> Set.empty (module Int)

let rec replace hole repl = function
  | Variable _ as v -> v
  | Arrow (l, r) -> Arrow (replace hole repl l, replace hole repl r)
  | NamedLabel (lbl, ps) -> NamedLabel (lbl, List.map ps ~f:(replace hole repl))
  | Hole h as orig -> if Int.equal h.id hole.id then repl else orig

let rec instantiate inst_id = function
  | Variable v -> CVar (v, inst_id)
  | Arrow (l, r) -> CArrow (instantiate inst_id l, instantiate inst_id r)
  | NamedLabel (lbl, ps) -> CLabel (lbl, List.map ps ~f:(instantiate inst_id))
  | Hole h -> Instantiation (h.id, inst_id)

let add_param_holes label_arities =
  let rec go ~under_arrow = function
    | Arrow (l, r) -> Arrow (go ~under_arrow:true l, go ~under_arrow:true r)
    | NamedLabel (lbl, ps) -> (
        match Map.find label_arities lbl with
        | Some n when List.is_empty ps && n > 0 ->
            let params =
              List.init n ~f:(fun _ ->
                  if under_arrow then make_hole `TypeHole
                  else make_hole ~label_only:false `Blank)
            in
            NamedLabel (lbl, params)
        | _ -> NamedLabel (lbl, List.map ps ~f:(go ~under_arrow)))
    | Hole _ as h -> h
    | Variable _ as v -> v
  in
  go ~under_arrow:false

module SearchState = struct
  type t = {
    names : (string, int, String.comparator_witness) Map.t;
    types : rec_type list;
    rounds : int list;
    label_arities : (int, int, Int.comparator_witness) Map.t;
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
      names = Map.empty (module String);
      types = [];
      rounds = [];
      label_arities = Map.empty (module Int);
      id = next_id ();
    }

  let create ?(names = Map.empty (module String)) ?(types = []) ?(rounds = [])
      ?(label_arities = Map.empty (module Int)) () =
    { names; types; rounds; label_arities; id = next_id () }

  let map_types t ~f = { t with types = List.map t.types ~f }
  let map_types_i t ~f = { t with types = List.mapi t.types ~f }

  let map_types_set_arities t ~arities ~f =
    { t with types = List.map t.types ~f; label_arities = arities }

  let type_of t name = List.nth_exn t.types (Map.find_exn t.names name)

  let blanks t =
    List.concat_map t.types ~f:(fun ty ->
        all_holes ty
        |> List.filter ~f:(fun h -> match h.kind with Blank _ -> true | _ -> false))

  let no_fillable t =
    List.for_all t.types ~f:(fun ty -> Option.is_none (shallowest_fillable ty))

  let no_holes t = List.for_all t.types ~f:no_holes

  let max_param_height t =
    List.max_elt t.types ~compare:(fun a b ->
        Int.compare
          (max_param_height ~count_arrow:false a)
          (max_param_height ~count_arrow:false b))
    |> Option.value ~default:0

  let fn_arities t =
    Map.map t.names ~f:(fun idx ->
        let ty = List.nth_exn t.types idx in
        let rec count acc = function
          | Arrow (_, r) -> count (acc + 1) r
          | _ -> acc
        in
        count 0 ty)

  let as_map t =
    Map.map t.names ~f:(fun idx -> List.nth_exn t.types idx)
end
