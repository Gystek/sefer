type literal =
  | Integer of int

type 'a expr =
  | Literal of 'a * literal
  | Tuple of 'a * 'a expr list
  | Variable of 'a * string
  | Application of 'a * 'a expr * 'a expr list
  | Abstraction of 'a * ('a * string) list * 'a expr
  | Let of 'a * ('a * string) * 'a expr * 'a expr
  | If of 'a * 'a expr * 'a expr * 'a expr

type locexprt = Type.loctyp expr
