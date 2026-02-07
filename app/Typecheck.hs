{-# LANGUAGE NamedFieldPuns #-}
module Typecheck ( Typechecker(..), initTC ) where

import Control.Monad.Except
import Control.Comonad.Cofree
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
                   , bindings :: Map Text Type0
                   , eqs :: [(Type0, Type0)]
                   , subst :: Map Int Type0
                   , scs :: [Constructor]
                   , adts :: [ADType]
                   }

data TCError = HeteroPrim Type0 Type0
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

addEq :: Type0 -> Type0 -> StateT Typechecker Result ()
addEq x y = do
  tc@Typechecker { eqs } <- get
  put tc { eqs = (x,y):eqs }
  pure ()

unify :: Location -> StateT Typechecker Result ()
unify _ = pure () -- TODO

applySubsts :: LocExprTP0 -> StateT Typechecker Result LocExprTP0
applySubsts e = do
  tc@Typechecker { subst } <- get
  pure $ Data.HashMap.foldWithKey applySubst e subst

applySubstT :: Int -> Type0 -> Type0 -> Type0
applySubstT i t1 (Type.Variable j)
  | i == j = t1
  | otherwise = (Type.Variable j)
applySubstT i t1 (Type.Tuple ts) = Type.Tuple $ flip Prelude.map ts $ applySubstT i t1
applySubstT i t1 (Type.Fun args et) = flip Type.Fun (applySubstT i t1 et) $ flip Prelude.map args $ applySubstT i t1
applySubstT i t1 (Type.Data d ts) = Type.Data d $ flip Prelude.map ts $ applySubstT i t1
applySubstT _ _ t = t

applySubst :: Int -> Type0 -> LocExprTP0 -> LocExprTP0
applySubst _ _ e@((Nothing, _) :< _) = e
applySubst i t1 ((Just t, loc) :< Expr.Tuple args) = (:<) (Just $ applySubstT i t1 t, loc) $ Expr.Tuple $ flip Prelude.map args $ applySubst i t1
applySubst i t1 ((Just t, loc) :< Expr.Const k args) = (:<) (Just $ applySubstT i t1 t, loc) $ Expr.Const k $ flip Prelude.map args $ applySubst i t1
applySubst i t1 ((Just t, loc) :< Expr.App f args) = (:<) (Just $ applySubstT i t1 t, loc) $ Expr.App (applySubst i t1 f) $ flip Prelude.map args $ applySubst i t1
applySubst i t1 ((Just t, loc) :< Expr.Abs args e) = (:<) (Just $ applySubstT i t1 t, loc) $ flip Expr.Abs (applySubst i t1 e) $ flip Prelude.map args $ applySubst i t1
applySubst i t1 ((Just t, loc) :< Expr.Let x y z) = (Just $ applySubstT i t1 t, loc) :< Expr.Let (applySubst i t1 x) (applySubst i t1 y) (applySubst i t1 z)
applySubst i t1 ((Just t, loc) :< Expr.Cond x y z) = (Just $ applySubstT i t1 t, loc) :< Expr.Cond (applySubst i t1 x) (applySubst i t1 y) (applySubst i t1 z)
applySubst i t1 ((Just t, loc) :< Expr.Match e ps) = (:<) (Just $ applySubstT i t1 t, loc) $ Expr.Match (applySubst i t1 e) $ flip Prelude.map ps $ allThree $ applySubst i t1
applySubst i t1 ((Just t, loc) :< e) = (Just $ applySubstT i t1 t, loc) :< e

extractType :: LocExprTP0 -> Type0
extractType ((Just t, _) :< _) = t

getBindingType :: LocExprTP0 -> (Text, Type0)
getBindingType ((Just t, _) :< Expr.Binding x) = (x, t)

checkLists :: Location -> [Type0] -> [Type0] -> StateT Typechecker Result ()
checkLists loc (x:xs) (y:ys) = addEq x y >> checkLists loc xs ys
checkLists loc [] [] = unify loc

tcExpr :: LocExprTP0 -> StateT Typechecker Result LocExprTP0
tcExpr e@((t, loc) :< Literal l) = let tt = getType0 l
                                 in case t of
                                      Nothing -> pure $ (Just tt, loc) :< Literal l
                                      Just (Type.Variable i) -> do
                                        addEq (Type.Variable i) tt
                                        unify loc
                                        pure e
                                      Just t | t == tt -> pure e
                                             | otherwise -> throwError (loc, HeteroPrim t tt)
tcExpr ((t, loc) :< Expr.Tuple el) = do
  ela <- mapM tcExpr el
  let targs = Prelude.map extractType ela
  case t of
    Nothing -> pure $ (Just $ Type.Tuple targs, loc) :< Expr.Tuple ela
    Just (Type.Variable i) -> do
      addEq (Type.Variable i) (Type.Tuple targs)
      unify loc
      pure $ (t, loc) :< Expr.Tuple ela
    Just (Type.Tuple targs1) -> do
      if Prelude.length targs /= Prelude.length targs1
      then throwError (loc, TupleArity (Prelude.length targs) (Prelude.length targs1))
      else checkLists loc targs targs1
      pure $ (Just $ Type.Tuple targs, loc) :< Expr.Tuple ela
    Just t -> throwError (loc, HeteroPrim t $ Type.Tuple targs)
-- TODO: handle currying
tcExpr ((t, loc) :< Expr.App ((tf, loc1) :< Expr.Abs fargs expr) cargs) = do
  ctargs <- mapM tcExpr cargs
  let f = (tf, loc1) :< Expr.Abs fargs expr
  ft <- tcExpr f
  let (_ :< Expr.Abs ftargs exprt) = ft
  -- (\xyz -> e) a b c |- t(x) = t(a), t(y) = t(b), t(z) = t(c)
  let targs = Prelude.map extractType ftargs
  let tcargs = Prelude.map extractType ctargs
  if Prelude.length targs /= Prelude.length tcargs
  then throwError (loc, CallArity (Prelude.length targs) (Prelude.length tcargs))
  else checkLists loc targs tcargs -- unifies
  let te = extractType exprt
  let e = (Just te, loc) :< Expr.App ft ctargs
  case t of
    Nothing -> pure e
    Just t -> do
      addEq t (extractType exprt)
      unify loc
      pure e
tcExpr ((t, loc) :< Expr.App f cargs) = do
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
  let e = (Just tr, loc) :< Expr.App ft ctargs
  case t of
    Nothing -> pure e
    Just t -> do
      addEq t tr
      unify loc
      pure e
tcExpr ((t, loc) :< Expr.Abs fargs expr) = do
  ftargs <- mapM tcExpr fargs
  let targs = Prelude.map extractType ftargs
  tc@Typechecker { bindings } <- get
  let nb = flip Data.HashMap.union bindings $ Data.HashMap.fromList $ Prelude.map getBindingType ftargs
  put tc { bindings = nb }
  exprt <- tcExpr expr
  put tc { bindings }
  let tr = extractType exprt
  let te = Type.Fun targs tr
  let et = (Just te, loc) :< Expr.Abs ftargs exprt
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
tcExpr ((t, loc) :< Expr.Const i args) = do
  argst <- mapM tcExpr args
  tc@Typechecker { scs, adts } <- get
  let k = scs !! i
  let adt = adts !! parent k
  let targs = Prelude.drop (nVar adt) . Prelude.map extractType $ argst
  let tk = Type.Data (parent k) targs
  let kt = (Just tk, loc) :< Expr.Const i argst
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
tcExpr ((t, loc) :< Expr.Let x y z) = do
  xt <- tcExpr x
  yt <- tcExpr y
  let (Just tx, _) :< Expr.Binding xb = xt
  addEq tx (extractType yt)
  unify loc
  tc@Typechecker { bindings } <- get
  let nb = Data.HashMap.insert xb tx bindings
  put tc { bindings = nb }
  zt <- tcExpr z
  tc <- get
  put tc { bindings }
  let tz = extractType zt
  case t of
    Nothing -> pure $ (Just tz, loc) :< Expr.Let xt yt zt
    Just t -> do
      addEq t tz
      unify loc
      pure $ (Just t, loc) :< Expr.Let xt yt zt
tcExpr ((t, loc) :< Expr.Cond ei et ee) = do
  eit <- tcExpr ei
  ett <- tcExpr et
  eet <- tcExpr ee
  addEq (extractType ett) (extractType eet)
  addEq (extractType eit) Type.Boolean
  unify loc
  case t of
    Nothing -> pure $ (Just . extractType $ ett, loc) :< Expr.Cond eit ett eet
    Just t -> do
      addEq t (extractType ett)
      unify loc
      pure $ (Just t, loc) :< Expr.Cond eit ett eet
tcExpr ((Nothing, loc) :< Expr.Binding x) = do
  i <- newVar
  pure $ (Just $ Type.Variable i, loc) :< Expr.Binding x
tcExpr e@((t@(Just _), loc) :< Expr.Binding _) = pure e
tcExpr e@((t0, loc) :< Expr.Var x) = do
  tc@Typechecker { bindings } <- get
  case Data.HashMap.lookup x bindings of
    Nothing -> throwError (loc, Unbound x)
    Just t1 -> case t0 of
                 Nothing -> pure $ (Just t1, loc) :< Expr.Var x
                 Just t0 -> do
                   addEq t0 t1
                   unify loc
                   pure e
tcExpr ((t, loc) :< Expr.Match e ps) = do
  et <- tcExpr e
  pst <- mapM (tcPattern et) ps
  let pe = Prelude.map (both extractType . \(x, _, z) -> (x, z)) pst
  mapM_ (uncurry addEq) $ pairs $ Prelude.map fst pe
  mapM_ (uncurry addEq) $ pairs $ Prelude.map snd pe
  unify loc
  let tr = snd . Prelude.head $ pe
  let e = (Just tr, loc) :< Expr.Match et pst
  case t of
    Nothing -> pure e
    Just t -> do
      addEq t tr
      unify loc
      pure e

tcPattern :: LocExprTP0 -> (LocExprTP0, LocExprTP0, LocExprTP0) -> StateT Typechecker Result (LocExprTP0, LocExprTP0, LocExprTP0)
tcPattern e0 (p, c, e) = do
  pt <- tcExpr p
  addEq (extractType e0) (extractType pt)
  tc@Typechecker { bindings } <- get
  let nb = flip Data.HashMap.union bindings $ Data.HashMap.fromList $ getPatternBindings pt
  put tc { bindings = nb }
  ct <- tcExpr c
  et <- tcExpr e
  put tc { bindings }
  addEq (extractType ct) Type.Boolean
  pure (pt, ct, et)

getPatternBindings :: LocExprTP0 -> [(Text, Type0)]
getPatternBindings (_ :< Expr.Literal _) = []
getPatternBindings (_ :< Expr.Tuple targs) = Prelude.concat $ Prelude.map getPatternBindings targs
getPatternBindings ((Just t, _) :< Expr.Binding x) = [(x, t)]
getPatternBindings (_ :< Expr.Const _ targs) = Prelude.concat $ Prelude.map getPatternBindings targs
