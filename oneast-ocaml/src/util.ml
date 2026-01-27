open Base

module Counter = struct
  type t = { mutable n : int }

  let create () = { n = 0 }
  let get t =
    let v = t.n in
    t.n <- v + 1;
    v

  let ensure_gt t k = if t.n <= k then t.n <- k + 1
end

module IntUnionFind = struct
  type t = { parent : (int, int) Hashtbl.t; size : (int, int) Hashtbl.t }

  let create () = { parent = Hashtbl.create (module Int); size = Hashtbl.create (module Int) }

  let rec find t x =
    match Hashtbl.find t.parent x with
    | None ->
        Hashtbl.set t.parent ~key:x ~data:x;
        Hashtbl.set t.size ~key:x ~data:1;
        x
    | Some p ->
        if Int.equal p x then x
        else
          let r = find t p in
          Hashtbl.set t.parent ~key:x ~data:r;
          r

  let union t a b =
    let ra = find t a and rb = find t b in
    if Int.equal ra rb then ()
    else
      let sa = Hashtbl.find_exn t.size ra and sb = Hashtbl.find_exn t.size rb in
      if sa < sb then (
        Hashtbl.set t.parent ~key:ra ~data:rb;
        Hashtbl.set t.size ~key:rb ~data:(sa + sb))
      else (
        Hashtbl.set t.parent ~key:rb ~data:ra;
        Hashtbl.set t.size ~key:ra ~data:(sa + sb))
end

module Logger = struct
  type t = { counts : (string, int) Hashtbl.t }

  let create () = { counts = Hashtbl.create (module String) }

  let count t msg =
    let v = Option.value (Hashtbl.find t.counts msg) ~default:0 in
    Hashtbl.set t.counts ~key:msg ~data:(v + 1)

  let dump t =
    Hashtbl.iteri t.counts ~f:(fun ~key ~data ->
        Stdio.printf "[log] %s -> %d\n%!" key data)
end

module Oracle = struct
  type t = { equal : string -> string -> bool }

  let default = { equal = String.equal }
  let equal t a b = t.equal a b
end
