let rec mapM (f : 'a -> ('b, 'e) result) : 'a list -> ('b list, 'e) result =
  function
  | [] -> Ok []
  | x :: x' ->
      Result.bind (f x) (fun y -> mapM f x' |> Result.map (fun y' -> y :: y'))

let ( >>= ) = Result.bind
