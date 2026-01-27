open Base
open Types
open Util

module EnumerateOneAST = struct
  let rec fast_forward (candidate : SearchState.t) : SearchState.t option =
    let rec ff_type t u =
      let changes = Types.all_holes t |> List.map ~f:(fun h -> (h, None)) in
      let changed = ref false in
      let t' =
        List.fold changes ~init:t ~f:(fun acc (h, ty_opt) ->
            match ty_opt with
            | None -> acc
            | Some ty ->
                changed := true;
                Types.replace h ty acc)
      in
      (t', !changed)
    in
    let rec loop curr =
      let u = Unification.create curr [] in
      let changed_any = ref false in
      let types' =
        List.map curr.SearchState.types ~f:(fun t ->
            let t', changed = ff_type t u in
            if changed then changed_any := true;
            t')
      in
      let curr' = { curr with types = types' } in
      if !changed_any then loop curr' else curr'
    in
    let res = loop candidate in
    if SearchState.no_holes res then Some res else None

  let rec commit c ~unification ~introduce_blanks ~fast_forward_blanks ~size_bound
      ~hard_depth_bound ~logging_seed =
    if SearchState.no_holes c then Sequence.singleton c
    else if SearchState.no_fillable c then
      if fast_forward_blanks then Sequence.of_list (Option.to_list (fast_forward c)) else Sequence.singleton c
    else if Int.equal size_bound 0 then Sequence.of_list (Option.to_list (fast_forward c))
    else
      let holes =
        c.SearchState.types
        |> List.mapi ~f:(fun idx ty -> (idx, Types.shallowest_fillable ty))
        |> List.filter_map ~f:(fun (i, h_opt) ->
               Option.map h_opt ~f:(fun hd -> (i, hd)))
      in
      let i_to_fill, (hole, depth) =
        List.min_elt holes ~compare:(fun (_, (_, d1)) (_, (_, d2)) -> Int.compare d1 d2)
        |> Option.value_exn
      in
      let expansions =
        let vars = Set.length (Types.variables (List.nth_exn c.types i_to_fill)) in
        match hole.kind with
        | Blank _ -> [ Types.Hole hole ]
        | TypeHole ->
            let var_exps = List.init (vars + 1) ~f:(fun v -> Types.Variable v) in
            let fn_exp = Types.Arrow (Types.make_hole `TypeHole, Types.make_hole `TypeHole) in
            let label_exps =
              Map.to_alist c.label_arities
              |> List.map ~f:(fun (lbl, ar) ->
                     Types.NamedLabel (lbl, List.init ar ~f:(fun _ -> Types.make_hole `TypeHole)))
            in
            var_exps @ (fn_exp :: label_exps)
      in
      Sequence.of_list expansions
      |> Sequence.map ~f:(fun exp ->
             SearchState.map_types_i c ~f:(fun i p ->
                 if Int.equal i i_to_fill then Types.replace hole exp p else p))
      |> Sequence.filter_map ~f:(fun cand ->
             let u = Unification.create cand [] in
             if Unification.ok u then Some (cand, u) else None)
      |> Sequence.concat_map ~f:(fun (cand, u) ->
             Util.Logger.count logging_seed "[commit] candidates";
             commit cand ~unification:u ~introduce_blanks ~fast_forward_blanks ~size_bound:(size_bound - 1)
               ~hard_depth_bound ~logging_seed)
end
