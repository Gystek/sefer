let rec mapM (f : 'a -> ('b, 'e) result) : 'a list -> ('b list, 'e) result =
  function
  | [] -> Ok []
  | x :: x' ->
      Result.bind (f x) (fun y -> mapM f x' |> Result.map (fun y' -> y :: y'))

let rec mapM2 (f : 'a -> 'b -> ('c, 'e) result) (xs : 'a list) (ys : 'b list) :
    ('c list, 'e) result =
  match (xs, ys) with
  | [], _ | _, [] -> Ok []
  | x :: x', y :: y' ->
      Result.bind (f x y) (fun z ->
          mapM2 f x' y' |> Result.map (fun z' -> z :: z'))

let ( >>= ) = Result.bind
let map_fst (f : 'a -> 'c) : 'a * 'b -> 'c * 'b = function x, y -> (f x, y)
let map_snd (f : 'b -> 'c) : 'a * 'b -> 'a * 'c = function x, y -> (x, f y)
