type typ =
  | Integer
  | Tuple of typ list
  | Arrow of typ list * typ
  | Forall of int * typ
  | Variable of int

type loctyp = typ option Location.located
