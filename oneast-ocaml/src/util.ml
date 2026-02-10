open Stdlib

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
  module H = Hashtbl.Make (struct
    type t = int

    let equal = ( = )
    let hash = Hashtbl.hash
  end)

  type t = { parent : int H.t; size : int H.t }

  let create () = { parent = H.create 16; size = H.create 16 }

  let rec find t x =
    match H.find_opt t.parent x with
    | None ->
        H.replace t.parent x x;
        H.replace t.size x 1;
        x
    | Some p ->
        if p = x then x
        else
          let r = find t p in
          H.replace t.parent x r;
          r

  let union t a b =
    let ra = find t a and rb = find t b in
    if ra = rb then ()
    else
      let sa = H.find_opt t.size ra |> Option.value ~default:1
      and sb = H.find_opt t.size rb |> Option.value ~default:1 in
      if sa < sb then (
        H.replace t.parent ra rb;
        H.replace t.size rb (sa + sb))
      else (
        H.replace t.parent rb ra;
        H.replace t.size ra (sa + sb))
end

module Logger = struct
  module H = Hashtbl.Make (struct
    type t = string

    let equal = String.equal
    let hash = Hashtbl.hash
  end)

  type t = { counts : int H.t }

  let create () = { counts = H.create 16 }

  let count t msg =
    let v = Option.value ~default:0 (H.find_opt t.counts msg) in
    H.replace t.counts msg (v + 1)

  let dump t =
    H.iter (fun k v -> Printf.printf "[log] %s -> %d\n%!" k v) t.counts
end

module Oracle = struct
  type t = { equal : string -> string -> bool }

  let default = { equal = String.equal }
  let equal t a b = t.equal a b
end
