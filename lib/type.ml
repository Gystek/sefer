type typ =
  | Integer
  | Boolean
  | Tuple of typ list
  | Arrow of typ * typ
  | Forall of int * typ
  | Var of int

let rec size : typ -> int = function
  | Var _ -> 0
  | Integer | Boolean -> 1
  | Tuple xs -> List.length xs + (List.map size xs |> List.fold_left ( + ) 0)
  | Arrow (t, t') -> 2 + size t + size t'
  | Forall (_, t) -> 1 + size t

type loctyp = typ option Location.located

let rec string_of_typ : typ -> string = function
  | Var i -> "α" ^ string_of_int i
  | Forall (i, t) -> "∀α" ^ string_of_int i ^ "." ^ string_of_typ t
  | Arrow (t, t') -> string_of_typ t ^ " → " ^ string_of_typ t'
  | Tuple ts ->
      List.map string_of_typ ts |> String.concat " * " |> fun x -> "(" ^ x ^ ")"
  | Integer -> "ℕ"
  | Boolean -> "𝔹"
