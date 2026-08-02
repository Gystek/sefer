type literal = Integer of int | Boolean of bool

type 'a expr =
  | Literal of literal
  | Tuple of 'a list
  | Variable of string
  | Application of 'a * 'a list
  | Abstraction of (string * Type.typ option) list * 'a
  | Let of string * 'a * 'a
  | If of 'a * 'a * 'a

type locexprt = { ann : Type.loctyp; exp : locexprt expr }

let get_type e = snd e.ann |> Option.get
