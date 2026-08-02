type typ =
  | Integer
  | Boolean
  | Tuple of typ list
  | Arrow of typ list * typ
  | Forall of int * typ
  | Var of int

type loctyp = typ option Location.located
