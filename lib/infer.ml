open Expr
open Location
open Type
open Utils

type tcerror =
  | Unbound of string
  | ArityMismatch of typ list * typ list
  | UnifyFail of typ * typ
  | InfiniteType of int * typ
  | MissingAnnot of locexprt

type 'a tcresult = ('a, tcerror located) result

type tc = {
  mutable nv : int;
  ctx : (string, typ) Hashtbl.t;
  vars : (int, typ) Hashtbl.t;
}

let init_tc () : tc =
  { nv = 0; ctx = Hashtbl.create 20; vars = Hashtbl.create 20 }

let newvar tc : typ =
  tc.nv <- tc.nv + 1;
  let i = tc.nv - 1 in
  let t = Var i in
  Hashtbl.add tc.vars i t;
  t

let rec resolve tc : typ -> typ = function
  | Var i -> find_var tc i
  | Forall (_, t) -> resolve tc t
  | Arrow (t, t') -> Arrow (resolve tc t, resolve tc t')
  | Tuple ts -> Tuple (List.map (resolve tc) ts)
  | t -> t

and find_var tc i : typ =
  let t = Hashtbl.find tc.vars i in
  if t = Var i then t
  else
    let t' = resolve tc t in
    Hashtbl.replace tc.vars i t';
    t'

let union_vars tc i j : typ =
  let t = find_var tc i and t' = find_var tc j in
  let s = size t and s' = size t' in
  if t <> t' then
    if s < s' then (
      Hashtbl.replace tc.vars i t';
      t')
    else (
      Hashtbl.replace tc.vars j t;
      t)
  else if s < s' then t'
  else t

let inst tc : typ -> typ =
  let rec inst' m = function
    | Var i -> ( match Hashtbl.find_opt m i with None -> Var i | Some t -> t)
    | Forall (i, t) ->
        Hashtbl.add m i (newvar tc);
        inst' m t
    | Arrow (t, t') -> Arrow (inst' m t, inst' m t')
    | Tuple ts -> Tuple (List.map (inst' m) ts)
    | t -> t
  in
  inst' (Hashtbl.create 20)

let rec occurs (i : int) : typ -> bool = function
  | Var j when i == j -> true
  | Forall (j, t) when i <> j -> occurs i t
  | Arrow (t, t') -> occurs i t || occurs i t'
  | Tuple ts -> List.exists (occurs i) ts
  | _ -> false

let rec unify tc loc (t : typ) (t' : typ) : typ tcresult =
  let t = resolve tc t and t' = resolve tc t' in
  match (t, t') with
  | Var i, Var j -> union_vars tc i j |> Result.ok
  | Var i, t | t, Var i ->
      if occurs i t then Error (loc, InfiniteType (i, t))
      else (
        Hashtbl.replace tc.vars i t;
        Ok t)
  | Arrow (t0, t1), Arrow (t0', t1') ->
      unify tc loc t0 t0' >>= fun t0'' ->
      unify tc loc t1 t1' |> Result.map (fun t1'' -> Arrow (t0'', t1''))
  | Tuple ts, Tuple ts' ->
      if List.length ts <> List.length ts' then
        Error (loc, ArityMismatch (ts, ts'))
      else mapM2 (unify tc loc) ts ts' |> Result.map (fun ts'' -> Tuple ts'')
  | Integer, Integer -> Ok Integer
  | Boolean, Boolean -> Ok Boolean
  | _ -> Error (loc, UnifyFail (t, t'))

let generalise tc t : typ =
  let rec generalise' fv = function
    | Var i ->
        if Hashtbl.find tc.vars i = Var i && not (List.mem i fv) then
          (i :: fv, Var i)
        else (fv, Var i)
    | Tuple ts ->
        map_snd
          (fun x -> Tuple (List.rev x))
          (List.fold_left
             (fun (fv, ts') t ->
               let fv', t' = generalise' fv t in
               (fv', t' :: ts'))
             (fv, []) ts)
    | Forall (i, t) -> generalise' (i :: fv) t
    | Arrow (t0, t1) ->
        let fv', t0' = generalise' fv t0 in
        let fv'', t1' = generalise' fv' t1 in
        (fv'', Arrow (t0', t1'))
    | t -> (fv, t)
  in
  let fv, t' = generalise' [] t in
  List.fold_left (fun t i -> Forall (i, t)) t' fv

let rec check tc (e : locexprt) : locexprt tcresult =
  match e.ann with
  | loc, Some t ->
      infer tc e >>= fun e' ->
      snd e'.ann |> Option.get |> unify tc loc t
      |> Result.map (fun t' -> { e' with ann = (fst e'.ann, Some t') })
  | _, None -> infer tc e

and infer tc e : locexprt tcresult =
  match e.exp with
  | Variable v -> (
      match Hashtbl.find_opt tc.ctx v with
      | None -> Error (fst e.ann, Unbound v)
      | Some s ->
          let t = inst tc s in
          Ok { e with ann = (fst e.ann, Some t) })
  | Application (f, args) ->
      check tc f >>= fun f' ->
      mapM (check tc) args >>= fun args' ->
      let t = newvar tc in
      List.map get_type args'
      |> (fun xs -> List.fold_right (fun t t' -> Arrow (t, t')) xs t)
      |> unify tc (fst e.ann) (get_type f')
      |> Result.map (fun tf ->
             {
               ann = (fst e.ann, Some t);
               exp = Application ({ f' with ann = (fst e.ann, Some tf) }, args');
             })
  | Abstraction (args, e) ->
      let argst =
        List.map (fun (v, t) -> (v, Option.value t ~default:(newvar tc))) args
      in
      List.iter (fun (v, t) -> Hashtbl.add tc.ctx v t) argst;
      check tc e
      |> Result.map (fun e' ->
             let t' = get_type e' in
             List.iter (fun (v, _) -> Hashtbl.remove tc.ctx v) argst;
             {
               ann =
                 ( fst e.ann,
                   Some
                     ( List.map snd argst |> fun xs ->
                       List.fold_right (fun t t' -> Arrow (t, t')) xs t' ) );
               exp = Abstraction (List.map (map_snd Option.some) argst, e');
             })
  | Let (x, y, z) ->
      check tc y >>= fun y' ->
      get_type y' |> generalise tc |> Hashtbl.add tc.ctx x;
      check tc z
      |> Result.map (fun z' ->
             let t' = get_type z' in
             Hashtbl.remove tc.ctx x;
             { ann = (fst e.ann, Some t'); exp = Let (x, y', z') })
  | Tuple els ->
      mapM (check tc) els
      |> Result.map (fun els' ->
             {
               ann = (fst e.ann, Some (Tuple (List.map get_type els')));
               exp = Tuple els';
             })
  | If (ei, et, ee) ->
      check tc ei >>= fun ei' ->
      unify tc (fst ei.ann) (get_type ei') Boolean >>= fun _ ->
      check tc et >>= fun et' ->
      check tc ee >>= fun ee' ->
      unify tc (fst ee.ann) (get_type et') (get_type ee')
      |> Result.map (fun t' ->
             {
               ann = (fst e.ann, Some t');
               exp =
                 If
                   ( ei',
                     { et' with ann = (fst et'.ann, Some t') },
                     { ee' with ann = (fst ee'.ann, Some t') } );
             })
  | Literal lit -> (
      match lit with
      | Integer _ -> Ok { e with ann = (fst e.ann, Some Integer) }
      | Boolean _ -> Ok { e with ann = (fst e.ann, Some Boolean) })

let rec gen_res_expr tc e : locexprt =
  let gen_res_expr' = function
    | Literal l -> Literal l
    | Tuple es -> Tuple (List.map (gen_res_expr tc) es)
    | Variable x -> Variable x
    | Application (f, xs) ->
        Application (gen_res_expr tc f, List.map (gen_res_expr tc) xs)
    | Abstraction (xs, e) -> Abstraction (xs, gen_res_expr tc e)
    | Let (x, y, z) -> Let (x, gen_res_expr tc y, gen_res_expr tc z)
    | If (ei, et, ee) ->
        If (gen_res_expr tc ei, gen_res_expr tc et, gen_res_expr tc ee)
  in
  let t' = get_type e |> resolve tc |> generalise tc
  and e' = gen_res_expr' e.exp in
  { ann = (fst e.ann, Some t'); exp = e' }

let rec gen_res_expr_it tc e =
  let e' = gen_res_expr tc e in
  if e' <> e then gen_res_expr_it tc e' else e

let run_tc tc e : locexprt tcresult =
  check tc e |> Result.map (gen_res_expr_it tc)
