type literal = Integer of int | Boolean of bool

let equal_literal l l' : bool =
  match (l, l') with
  | Integer i, Integer j -> i = j
  | Boolean b, Boolean c -> b = c
  | _ -> false

let pp_literal f : literal -> unit = function
  | Integer i -> Format.fprintf f "%d" i
  | Boolean b -> Format.fprintf f "%b" b

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
let get_exp e = e.exp

let rec pp fmt = function
  | Literal l -> pp_literal fmt l
  | Tuple [] -> Format.fprintf fmt "()"
  | Tuple (x :: xs) ->
      Format.fprintf fmt "(%a" pp (get_exp x);
      List.map get_exp xs |> List.iter (Format.fprintf fmt ", %a" pp);
      Format.fprintf fmt ")"
  | Variable x -> Format.fprintf fmt "%s" x
  | Application (f, xs) ->
      Format.fprintf fmt "%a" pp (get_exp f);
      List.map get_exp xs |> List.iter (Format.fprintf fmt " %a" pp)
  | Abstraction (xs, e) ->
      Format.fprintf fmt "(fun";
      List.iter
        (fun (x, t) ->
          match t with
          | None -> Format.fprintf fmt " %s" x
          | Some t -> Format.fprintf fmt " (%s : %a)" x Type.pp t)
        xs;
      Format.fprintf fmt " = ";
      Format.fprintf fmt "%a)" pp (get_exp e)
  | Let (x, y, z) ->
      Format.fprintf fmt "let %s = %a in %a" x pp (get_exp y) pp (get_exp z)
  | If (ei, et, ee) ->
      Format.fprintf fmt "if %a then %a else %a" pp (get_exp ei) pp (get_exp et)
        pp (get_exp ee)

let rec equal e e' : bool =
  match (e, e') with
  | Literal l, Literal l' -> equal_literal l l'
  | Tuple xs, Tuple xs' ->
      List.for_all2 equal (List.map get_exp xs) (List.map get_exp xs')
  | Variable x, Variable y -> x = y
  | Application (f, xs), Application (g, xs') ->
      let f' = get_exp f and g' = get_exp g in
      equal f' g'
      && List.for_all2 equal (List.map get_exp xs) (List.map get_exp xs')
  | Abstraction (xs, a), Abstraction (xs', b) ->
      let a' = get_exp a and b' = get_exp b in
      equal a' b'
      && List.for_all2
           (fun (x, t) (y, t') ->
             x = y
             &&
             match (t, t') with
             | Some t, Some t' -> Type.equal t t'
             | None, None -> true
             | _ -> false)
           xs xs'
  | Let (x, a, b), Let (x', c, d) ->
      let a' = get_exp a
      and b' = get_exp b
      and c' = get_exp c
      and d' = get_exp d in
      x = x' && equal a' c' && equal b' d'
  | If (a, b, c), If (x, y, z) ->
      let a' = get_exp a
      and b' = get_exp b
      and c' = get_exp c
      and x' = get_exp x
      and y' = get_exp y
      and z' = get_exp z in
      equal a' x' && equal b' y' && equal c' z'
  | _ -> false

let pp_locexpr fmt e =
  match e.ann with
  | l, None -> Format.fprintf fmt "%a: %a" Location.pp l pp e.exp
  | l, Some t ->
      Format.fprintf fmt "%a: %a [%a]" Location.pp l pp e.exp Type.pp t

let equal_locexpr e0 e1 =
  match (e0.ann, e1.ann) with
  | (l0, None), (l1, None) -> Location.equal l0 l1 && equal e0.exp e1.exp
  | (l0, Some t0), (l1, Some t1) ->
      Location.equal l0 l1 && Type.equal t0 t1 && equal e0.exp e1.exp
  | _ -> false
