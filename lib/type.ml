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

(* could be done more intelligently by treating
   α-equivalence as equality
 *)

let rec equal t t' : bool =
  match (t, t') with
  | Integer, Integer -> true
  | Boolean, Boolean -> true
  | Tuple ts, Tuple ts' -> List.for_all2 equal ts ts'
  | Arrow (t0, t1), Arrow (t0', t1') -> equal t0 t0' && equal t1 t1'
  | Forall (i, t), Forall (j, t') -> i = j && equal t t'
  | Var i, Var j -> i = j
  | _ -> false

let rec pp f : typ -> unit = function
  | Var i -> Format.fprintf f "α%d" i
  | Forall (i, t) -> Format.fprintf f "∀α%d.%a" i pp t
  | Arrow (t, t') -> Format.fprintf f "%a → %a" pp t pp t'
  | Tuple [] -> Format.fprintf f "()"
  | Tuple (t :: ts) ->
      Format.fprintf f "(%a" pp t;
      List.iter (Format.fprintf f " * %a" pp) ts;
      Format.fprintf f ")"
  | Integer -> Format.fprintf f "ℕ"
  | Boolean -> Format.fprintf f "𝔹"

let string_of_typ t : string = Format.sprintf "%a" t pp
