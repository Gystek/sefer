{-# LANGUAGE NamedFieldPuns #-}
module Typecheck ( Typechecker(..), initTC ) where

import Control.Monad.Except
import Control.Monad.State
import Data.HashMap
import Data.Text
import Data.Tuple.Extra
import Expr
import Literal
import Location
import Statement
import Type
import Utils

data Typechecker = Typechecker
                   { vg :: Int
                   , bindings :: Map Text Type
                   , eqs :: [(Type, Type)]
                   , subst :: Map Int Type
                   , scs :: [Constructor]
                   , adts :: [ADType]
                   }

data TCError = HeteroPrim Type Type
             | Unbound Text
             | TupleArity Int Int
             | FunArity Int Int
             | CallArity Int Int
             | WrongADT Int Int
             deriving (Show)

type Result = Either (Located TCError)

initTC :: [Constructor] -> [ADType] -> Typechecker
initTC scs adts = Typechecker { vg = 0
                              , bindings = Data.HashMap.empty
                              , eqs = []
                              , subst = Data.HashMap.empty
                              , scs
                              , adts
                              }

newVar :: StateT Typechecker Result Int
newVar = do
  tc@Typechecker { vg = x } <- get
  put tc { vg = x + 1 }
  pure x

addEq :: Type -> Type -> StateT Typechecker Result ()
addEq x y = do
  tc@Typechecker { eqs } <- get
  put tc { eqs = (x,y):eqs }
  pure ()

unify :: Location -> StateT Typechecker Result ()
unify _ = pure () -- TODO

applySubsts :: LocExprT -> StateT Typechecker Result LocExprT
applySubsts e = do
  tc@Typechecker { subst } <- get
  pure $ Data.HashMap.foldWithKey applySubst e subst

applySubstB :: Int -> Type -> Branch (Maybe Type, Location) -> Branch (Maybe Type, Location)
applySubstB i t1 Branch { pat, guard, body } = Branch { pat, guard = applySubst i t1 <$> guard, body = applySubst i t1 body }

applySubstT :: Int -> Type -> Type -> Type
applySubstT i t1 (Type.Variable j)
  | i == j = t1
  | otherwise = Type.Variable j
applySubstT i t1 (Type.Tuple ts) = Type.Tuple $ flip Prelude.map ts $ applySubstT i t1
applySubstT i t1 (Type.Fun args et) = flip Type.Fun (applySubstT i t1 et) $ flip Prelude.map args $ applySubstT i t1
applySubstT i t1 (Type.Data d ts) = Type.Data d $ flip Prelude.map ts $ applySubstT i t1
applySubstT _ _ t = t

applySubst :: Int -> Type -> LocExprT -> LocExprT
applySubst i t1 (Expr.Tuple (Just t, loc) args) = Expr.Tuple (Just $ applySubstT i t1 t, loc) $ flip Prelude.map args $ applySubst i t1
applySubst i t1 (Expr.Const (Just t, loc) k args) = Expr.Const (Just $ applySubstT i t1 t, loc) k $ flip Prelude.map args $ applySubst i t1
applySubst i t1 (Expr.App (Just t, loc) f args) = Expr.App (Just $ applySubstT i t1 t, loc) (applySubst i t1 f) $ flip Prelude.map args $ applySubst i t1
applySubst i t1 (Expr.Abs (Just t, loc) args e) = flip (Expr.Abs $ (Just $ applySubstT i t1 t, loc)) (applySubst i t1 e) $ flip Prelude.map args $ \(x, (tx, xl)) -> (x, (applySubstT i t1 <$> tx, xl))
applySubst i t1 (Expr.Let (Just t, loc) (x, (tx, xl)) y z) =  Expr.Let (Just $ applySubstT i t1 t, loc) (x, (applySubstT i t1 <$> tx, xl)) (applySubst i t1 y) (applySubst i t1 z)
applySubst i t1 (Expr.Cond (Just t, loc) x y z) = Expr.Cond (Just $ applySubstT i t1 t, loc) (applySubst i t1 x) (applySubst i t1 y) (applySubst i t1 z)
applySubst i t1 (Expr.Match (Just t, loc) e bs) = Expr.Match (Just $ applySubstT i t1 t, loc) (applySubst i t1 e) $ flip Prelude.map bs $ applySubstB i t1
applySubst i t1 (Expr.Literal (Just t, loc) lit) = Expr.Literal (Just $ applySubstT i t1 t, loc) lit
applySubst i t1 e = case ann e of
                      (Nothing, _) -> e

extractType :: LocExprT -> Type
extractType e = case ann e of
                  (Just t, _) -> t

checkLists :: Location -> [Type] -> [Type] -> StateT Typechecker Result ()
checkLists loc (x:xs) (y:ys) = addEq x y >> checkLists loc xs ys
checkLists loc [] [] = unify loc

tcExpr :: LocExprT -> StateT Typechecker Result LocExprT
tcExpr e@(Literal (t, loc) l) = let tt = getType l
                                in case t of
                                     Nothing -> pure $ Literal (Just tt, loc) l
                                     Just (Type.Variable i) -> do
                                       addEq (Type.Variable i) tt
                                       unify loc
                                       pure e
                                     Just t | t == tt -> pure e
                                            | otherwise -> throwError (loc, HeteroPrim t tt)
tcExpr (Expr.Tuple (t, loc) el) = do
  ela <- mapM tcExpr el
  let targs = Prelude.map extractType ela
  case t of
    Nothing -> pure $ Expr.Tuple (Just $ Type.Tuple targs, loc) ela
    Just (Type.Variable i) -> do
      addEq (Type.Variable i) (Type.Tuple targs)
      unify loc
      pure $ Expr.Tuple (t, loc) ela
    Just (Type.Tuple targs1) -> do
      if Prelude.length targs /= Prelude.length targs1
      then throwError (loc, TupleArity (Prelude.length targs) (Prelude.length targs1))
      else checkLists loc targs targs1
      pure $ Expr.Tuple (Just $ Type.Tuple targs, loc) ela
    Just t -> throwError (loc, HeteroPrim t $ Type.Tuple targs)
-- TODO: handle currying
tcExpr (Expr.App (t, loc) (Expr.Abs (tf, loc1) fargs expr) cargs) = do
  ctargs <- mapM tcExpr cargs
  let f = Expr.Abs (tf, loc1) fargs expr
  ft <- tcExpr f
  let (Expr.Abs _ ftargs exprt) = ft
  -- (\xyz -> e) a b c |- t(x) = t(a), t(y) = t(b), t(z) = t(c)
  let targs = Prelude.map (fromJust . fst . snd) ftargs
  let tcargs = Prelude.map extractType ctargs
  if Prelude.length targs /= Prelude.length tcargs
  then throwError (loc, CallArity (Prelude.length targs) (Prelude.length tcargs))
  else checkLists loc targs tcargs -- unifies
  let te = extractType exprt
  let e = Expr.App (Just te, loc) ft ctargs
  case t of
    Nothing -> pure e
    Just t -> do
      addEq t (extractType exprt)
      unify loc
      pure e
tcExpr (Expr.App (t, loc) f cargs) = do
  ctargs <- mapM tcExpr cargs
  ft <- tcExpr f
  tr <- case extractType ft of
    Type.Fun targs tr -> do
      if Prelude.length targs /= Prelude.length ctargs
        then throwError (loc, FunArity (Prelude.length targs) (Prelude.length ctargs))
        else checkLists loc targs $ Prelude.map extractType ctargs
      pure tr
    Type.Variable i -> do
      tr <- Type.Variable <$> newVar
      addEq (Type.Variable i) $ flip Type.Fun tr $ Prelude.map extractType ctargs
      pure tr
    t -> newVar >>= \i -> throwError (loc, HeteroPrim t $ flip Type.Fun (Type.Variable i) $ Prelude.map extractType ctargs)
  let e = Expr.App (Just tr, loc) ft ctargs
  case t of
    Nothing -> pure e
    Just t -> do
      addEq t tr
      unify loc
      pure e
tcExpr (Expr.Abs (t, loc) fargs expr) = do
  ftargs <- mapM tcBind fargs
  let targs = Prelude.map (fst . snd) ftargs
  tc@Typechecker { bindings } <- get
  let nb = flip Data.HashMap.union bindings $ Data.HashMap.fromList $ Prelude.map (\(x, (t, l)) -> (x, t)) ftargs
  put tc { bindings = nb }
  exprt <- tcExpr expr
  put tc { bindings }
  let tr = extractType exprt
  let te = Type.Fun targs tr
  let et = Expr.Abs (Just te, loc) (flip Prelude.map ftargs $ \(x, (t, l)) -> (x, (Just t, l))) exprt
  case t of
    Nothing -> pure et
    Just (Type.Fun targs1 tr1) -> do
      if Prelude.length targs /= Prelude.length targs1
        then throwError (loc, FunArity (Prelude.length targs) (Prelude.length targs1))
        else do
        addEq tr tr1
        checkLists loc targs targs1 -- unifies
        pure et
    Just (Type.Variable i) -> do
      addEq (Type.Variable i) te
      unify loc
      pure et
    Just t -> throwError (loc, HeteroPrim t te)
-- TODO: handle currying
tcExpr (Expr.Const (t, loc) i args) = do
  argst <- mapM tcExpr args
  tc@Typechecker { scs, adts } <- get
  let k = scs !! i
  let adt = adts !! parent k
  let targs = Prelude.drop (nVar adt) . Prelude.map extractType $ argst
  let tk = Type.Data (parent k) targs
  let kt = Expr.Const (Just tk, loc) i argst
  case t of
    Nothing -> pure kt
    Just (Type.Data ti targs1) -> if parent k /= ti
                                  then throwError (loc, WrongADT (parent k) ti)
                                  else do
      checkLists loc targs targs1 -- unifies
      pure kt
    Just (Type.Variable j) -> do
      addEq (Type.Variable j) tk
      unify loc
      pure kt
    Just t -> throwError (loc, HeteroPrim t tk)
tcExpr (Expr.Let (t, loc) x y z) = do
  (xt, (tx, xl)) <- tcBind x
  yt <- tcExpr y
  addEq tx (extractType yt)
  unify loc
  tc@Typechecker { bindings } <- get
  let nb = Data.HashMap.insert xt tx bindings
  put tc { bindings = nb }
  zt <- tcExpr z
  tc <- get
  put tc { bindings }
  let tz = extractType zt
  case t of
    Nothing -> pure $ Expr.Let (Just tz, loc) (xt, (Just tx, xl)) yt zt
    Just t -> do
      addEq t tz
      unify loc
      pure $ Expr.Let (Just t, loc) (xt, (Just tx, xl)) yt zt
tcExpr (Expr.Cond (t, loc) ei et ee) = do
  eit <- tcExpr ei
  ett <- tcExpr et
  eet <- tcExpr ee
  addEq (extractType ett) (extractType eet)
  addEq (extractType eit) Type.Boolean
  unify loc
  case t of
    Nothing -> pure $ Expr.Cond (Just . extractType $ ett, loc) eit ett eet
    Just t -> do
      addEq t (extractType ett)
      unify loc
      pure $ Expr.Cond (Just t, loc) eit ett eet
tcExpr e@(Expr.Var (t0, loc) x) = do
  tc@Typechecker { bindings } <- get
  case Data.HashMap.lookup x bindings of
    Nothing -> throwError (loc, Unbound x)
    Just t1 -> case t0 of
                 Nothing -> pure $ Expr.Var (Just t1, loc) x
                 Just t0 -> do
                   addEq t0 t1
                   unify loc
                   pure e
tcExpr (Expr.Match (t, loc) e ps) = do
  error "TODO"

tcBind :: (Text, (Maybe Type, Location)) -> StateT Typechecker Result (Text, (Type, Location))
tcBind (x, (Nothing, loc)) = do
  i <- newVar
  pure $ (x, (Type.Variable i, loc))
tcBind (x, (Just t, loc)) = pure $ (x, (t, loc))
