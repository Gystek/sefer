type 'a t = {
  parents : ('a, 'a) Hashtbl.t;
  size : 'a -> int;
  sizes : ('a, int) Hashtbl.t;
}

let create (n : int) (size : 'a -> int) : 'a t =
  { parents = Hashtbl.create n; sizes = Hashtbl.create n; size }

let insert (uf : 'a t) (x : 'a) : unit =
  if not (Hashtbl.mem uf.parents x) then Hashtbl.add uf.parents x x;
  Hashtbl.add uf.sizes x (uf.size x)

let rec find (uf : 'a t) (x : 'a) : 'a =
  let y = Hashtbl.find uf.parents x in
  if x = y then x
  else
    let y' = find uf y in
    Hashtbl.replace uf.parents x y';
    y'

let union (uf : 'a t) (x : 'a) (y : 'a) : 'a =
  let xs = Hashtbl.find uf.sizes x and ys = Hashtbl.find uf.sizes y in
  let x' = find uf x and y' = find uf y in
  if x' <> y' then
    let xs = Hashtbl.find uf.sizes x' and ys = Hashtbl.find uf.sizes y' in
    if xs < ys then (
      Hashtbl.replace uf.parents x' y';
      (* Hashtbl.replace uf.sizes y' (xs + ys); *)
      y')
    else (
      Hashtbl.replace uf.parents y' x';
      (* Hashtbl.replace uf.sizes x' (xs + ys); *)
      x')
  else if xs < ys then y' else x'

let has (uf : 'a t) (x : 'a) : bool = Hashtbl.mem uf.parents x
