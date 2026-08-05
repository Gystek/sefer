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
type tc = { mutable nv : int; ctx : (string, typ) Hashtbl.t; vars : typ Uf.t }

let init_tc () : tc = { nv = 0; ctx = Hashtbl.create 20; vars = Uf.create 20 }

let newvar tc : typ =
  tc.nv <- tc.nv + 1;
  Var (tc.nv - 1)

let inst tc : typ -> typ =
  let rec inst' m = function
    | Var i -> ( match Hashtbl.find_opt m i with None -> Var i | Some t -> t)
    | Forall (i, t) ->
        Hashtbl.add m i (newvar tc);
        inst' m t
    | Arrow (xs, t) -> Arrow (List.map (inst' m) xs, inst' m t)
    | Tuple ts -> Tuple (List.map (inst' m) ts)
    | t -> t
  in
  inst' (Hashtbl.create 20)

let rec occurs (i : int) : typ -> bool = function
  | Var j when i == j -> true
  | Forall (j, t) when i <> j -> occurs i t
  | Arrow (xs, t) -> occurs i t || List.exists (occurs i) xs
  | Tuple ts -> List.exists (occurs i) ts
  | _ -> false

let rec unify tc loc (t : typ) (t' : typ) : typ tcresult =
  Uf.insert tc.vars t;
  Uf.insert tc.vars t';
  let t : typ = Uf.find tc.vars t and t' : typ = Uf.find tc.vars t' in
  match (t, t') with
  | Var _, Var _ -> Uf.union tc.vars t t' |> Result.ok
  | Var i, t | t, Var i ->
      if occurs i t then Error (loc, InfiniteType (i, t))
      else Uf.union tc.vars t t' |> Result.ok
  | Arrow (xs, t), Arrow (ys, t') ->
      if List.length xs <> List.length ys then
        Error (loc, ArityMismatch (xs, ys))
      else
        mapM2 (unify tc loc) xs ys >>= fun zs ->
        unify tc loc t t' |> Result.map (fun t'' -> Arrow (zs, t''))
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
        (* is "bound to itself" free or not? is "bound to a free variable" free or not? *)
        if not (Uf.has tc.vars (Var i) || List.mem i fv) then (i :: fv, Var i)
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
    | Arrow (xs, t) ->
        let fv', xs' =
          List.fold_left
            (fun (fv, xs') t ->
              let fv', t' = generalise' fv t in
              (fv', t' :: xs'))
            (fv, []) xs
        in
        let fv'', t' = generalise' fv' t in
        (fv'', Arrow (List.rev xs', t'))
    | t -> (fv, t)
  in
  let fv, t' = generalise' [] t in
  List.fold_left (fun t i -> Forall (i, t)) t' fv

let rec check tc (e : locexprt) : locexprt tcresult =
  match e.ann with
  | loc, Some t ->
      infer tc e >>= fun e' ->
      snd e'.ann |> Option.get |> unify tc loc t |> Result.map (Fun.const e')
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
      unify tc (fst e.ann) (get_type f') (Arrow (List.map get_type args', t))
      |> Result.map (Fun.const { e with ann = (fst e.ann, Some t) })
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
               ann = (fst e.ann, Some (Arrow (List.map snd argst, t')));
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
      |> Result.map
           (Fun.const
              {
                ann = (fst e.ann, Some (get_type et'));
                exp = If (ei', et', ee');
              })
  | Literal lit -> (
      match lit with
      | Integer _ -> Ok { e with ann = (fst e.ann, Some Integer) }
      | Boolean _ -> Ok { e with ann = (fst e.ann, Some Boolean) })

let run_tc tc e : locexprt tcresult =
  check tc e
  |> Result.map (fun e' ->
         let t = get_type e' in
         let t' = generalise tc t in
         { e' with ann = (fst e.ann, Some t') })
