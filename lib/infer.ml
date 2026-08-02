open Expr
open Location
open Type
open Utils

type tcerror =
  | Unbound of string
  | UnifyFail of typ * typ
  | MissingAnnot of locexprt

type 'a tcresult = ('a, tcerror located) result
type tc = { mutable nv : int; ctx : (string, typ) Hashtbl.t }

let init_tc () : tc = { nv = 0; ctx = Hashtbl.create 20 }

let newvar tc : typ =
  !tc.nv <- !tc.nv + 1;
  Var (!tc.nv - 1)

let inst _tc : typ -> typ = function t -> t

let unify _tc loc t t' : typ tcresult =
  match (t, t') with _ -> Error (loc, UnifyFail (t, t'))

let generalise _tc : typ -> typ = function t -> t

let rec check tc (e : locexprt) : locexprt tcresult =
  match e.ann with
  | loc, Some t ->
      infer tc e >>= fun e' ->
      snd e'.ann |> Option.get |> unify tc loc t |> Result.map (Fun.const e')
  | _, None -> infer tc e

and infer tc e : locexprt tcresult =
  match e.exp with
  | Variable v -> (
      match Hashtbl.find_opt !tc.ctx v with
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
      List.iter (fun (v, t) -> Hashtbl.add !tc.ctx v t) argst;
      check tc e
      |> Result.map (fun e' ->
             let t' = get_type e' in
             List.iter (fun (v, _) -> Hashtbl.remove !tc.ctx v) argst;
             {
               ann = (fst e.ann, Some (Arrow (List.map snd argst, t')));
               exp = Abstraction (args, e');
             })
  | Let (x, y, z) ->
      check tc y >>= fun y' ->
      get_type y' |> generalise tc |> Hashtbl.add !tc.ctx x;
      check tc z
      |> Result.map (fun z' ->
             let t' = get_type z' in
             Hashtbl.remove !tc.ctx x;
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
