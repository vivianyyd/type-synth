open Types

module EnumerateOneAST = struct
  let fast_forward (candidate : SearchState.t) : SearchState.t option =
    let ff_type t _u =
      let changes = Types.all_holes t |> List.map (fun h -> (h, None)) in
      let changed = ref false in
      let t' =
        List.fold_left
          (fun acc (h, ty_opt) ->
            match ty_opt with
            | None -> acc
            | Some ty ->
                changed := true;
                Types.replace h ty acc)
          t changes
      in
      (t', !changed)
    in
    let rec loop curr =
      let u = Unification.create curr [] in
      let changed_any = ref false in
      let types' =
        List.map
          (fun t ->
            let t', changed = ff_type t u in
            if changed then changed_any := true;
            t')
          curr.SearchState.types
      in
      let curr' = { curr with types = types' } in
      if !changed_any then loop curr' else curr'
    in
    let res = loop candidate in
    if SearchState.no_holes res then Some res else None

  let expansions_for_hole ~hole ~label_arities ~vars ~must_be_leaf =
    match hole.kind with
    | Blank _ -> [ Types.Hole hole ]
    | TypeHole ->
        let var_exps = List.init (vars + 1) (fun v -> Types.Variable v) in
        let fn_exp =
          if must_be_leaf then []
          else [ Types.Arrow (Types.make_hole `TypeHole, Types.make_hole `TypeHole) ]
        in
        let label_exps =
          IntMap.bindings label_arities
          |> List.map (fun (lbl, ar) ->
                 Types.NamedLabel
                   (lbl, List.init ar (fun _ -> Types.make_hole `TypeHole)))
        in
        var_exps @ fn_exp @ label_exps

  let rec commit c ~introduce_blanks:_ ~fast_forward_blanks ~size_bound
      ~hard_depth_bound =
    if SearchState.no_holes c then [ c ]
    else if SearchState.no_fillable c then
      if fast_forward_blanks then
        (match fast_forward c with Some v -> [ v ] | None -> [])
      else [ c ]
    else if size_bound = 0 then (match fast_forward c with Some v -> [ v ] | None -> [])
    else
      let holes =
        c.SearchState.types
        |> List.mapi (fun idx ty -> (idx, Types.shallowest_fillable ty))
        |> List.filter_map (function
               | i, Some hd -> Some (i, hd)
               | _ -> None)
      in
      let i_to_fill, (hole, depth) =
        match holes with
        | [] -> failwith "no holes to fill"
        | h :: tl ->
            List.fold_left
              (fun ((_, (_, bd)) as best) (i, (h, d)) ->
                if d < bd then (i, (h, d)) else best)
              h tl
      in
      let vars =
        IntSet.cardinal (Types.variables (List.nth c.types i_to_fill))
      in
      let expansions =
        expansions_for_hole ~hole ~label_arities:c.label_arities ~vars
          ~must_be_leaf:(size_bound <= 1 || depth > hard_depth_bound)
      in
      List.concat_map
        (fun exp ->
          let cand =
            SearchState.map_types_i c ~f:(fun i p ->
                if i = i_to_fill then Types.replace hole exp p else p)
          in
          let u = Unification.create cand [] in
          if Unification.ok u then
            commit cand ~introduce_blanks:false ~fast_forward_blanks
              ~size_bound:(size_bound - 1) ~hard_depth_bound
          else [])
        expansions
end
