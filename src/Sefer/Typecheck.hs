{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
module Sefer.Typecheck ( Typechecker(..), TCError(..), initTC, runTC ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Foldable
import Data.Text
import Data.HashMap
import Data.Maybe
import Data.Text
import qualified Sefer.Expr as Expr
import qualified Sefer.Literal as Literal
import Sefer.Location
import qualified Sefer.Pattern as Pattern
import qualified Sefer.Type as Type
import Sefer.Statement
import Sefer.Utils
import qualified Data.List.Extra as Data.List
import Sefer.Type (TypeVar)
import qualified Control.Exception as Type
import Sefer.Expr (Expr(fargs))

data Typechecker = Typechecker
                   { vg :: Int
                   , lvl :: Int
                   , bindings :: Map Text Type.Type
                   , substs :: Map Int Type.Type
                   }
                   deriving Show

data TCError = HeteroPrim Type.Type Type.Type
             | Unbound Text
             | TupleArity Int Int
             | FunArity Int Int
--             | CallArity Int Int
             | ConstArity Int Int
             | WrongADT Int Int
             | UnifyFail Type.Type Type.Type
             | InfiniteType Type.Type
--             | MissingAnnotations Expr.LocExprT Expr.LocExprT Int
             deriving (Show, Eq)

type Result = Either (Located TCError)

initTC :: [Constructor] -> [ADType] -> Typechecker
initTC scs adts = Typechecker { vg = 0
                              , lvl = 1
                              , bindings = defaultBindings
                              , substs = Data.HashMap.empty
                              }

defaultBindings :: Map Text Type.Type
defaultBindings = Data.HashMap.fromList [ (pack "$addInt", Type.Fun [Type.Integer, Type.Integer] Type.Integer)
                                        ]

runTC :: StateT Typechecker Result ()
runTC = pure ()

-- utilities

newVar :: StateT Typechecker Result TypeVar
newVar = do
  tc@Typechecker { vg, lvl } <- get
  put tc { vg = vg + 1 }
  pure (vg, lvl)

occurs :: Location -> TypeVar -> Type.Type -> StateT Typechecker Result Type.Type 
occurs loc v t@(Type.Variable v')
  |  v == v' = throwError (loc, InfiniteType t)
occurs loc (vi, vl) (Type.Variable (i, l)) = do
  Typechecker { substs } <- get
  case Data.HashMap.lookup i substs of
    Just t -> occurs loc (vi, vl) t
    Nothing -> let l' = if member vi substs then l else min l vl
               in pure $ Type.Variable (i, l')
occurs loc v (Type.Tuple ts) = Type.Tuple <$> mapM (occurs loc v) ts 
occurs loc v (Type.Fun xs y) = Type.Fun <$> mapM (occurs loc v) xs <*> occurs loc v y
occurs loc v (Type.Data i ts) = Type.Data i <$> mapM (occurs loc v) ts
occurs _ _ t = pure t

-- typechecking
tvUnify :: Location -> TypeVar -> Type.Type -> StateT Typechecker Result ()
tvUnify loc (vi, vl) t = do
  tc@Typechecker { substs } <- get
  case Data.HashMap.lookup vi substs of
    Just t' -> unify loc t' t
    Nothing -> occurs loc (vi, vl) t >>= \t -> put tc { substs = insert vi t substs }

unify :: Location -> Type.Type -> Type.Type -> StateT Typechecker Result ()
unify _ t1 t2
  | t1 == t2 = pure ()
unify loc (Type.Variable v) t2 = tvUnify loc v t2
unify loc t1 (Type.Variable v) = tvUnify loc v t1
unify loc (Type.Tuple ts1) (Type.Tuple ts2)
  | Prelude.length ts1 /= Prelude.length ts2 = throwError (loc, TupleArity (Prelude.length ts1) (Prelude.length ts2))
  | otherwise = mapM_ (uncurry $ unify loc) $ Prelude.zip ts1 ts2
unify loc (Type.Fun xs1 y1) (Type.Fun xs2 y2)
  | Prelude.length xs1 /= Prelude.length xs2 = throwError (loc, FunArity (Prelude.length xs1) (Prelude.length xs2))
  | otherwise =  (mapM_ (uncurry $ unify loc) $ Prelude.zip xs1 xs2) >> unify loc y1 y2
unify loc (Type.Data i ts1) (Type.Data j ts2)
  | i /= j = throwError (loc, WrongADT i j)
  | Prelude.length ts1 /= Prelude.length ts2 = throwError (loc, ConstArity (Prelude.length ts1) (Prelude.length ts2))
  | otherwise =  mapM_ (uncurry $ unify loc) $ Prelude.zip ts1 ts2
unify loc t1 t2 = throwError (loc, UnifyFail t1 t2)

generalise :: Type.Type -> StateT Typechecker Result Type.Type
generalise t@(Type.Variable (vi, vl)) = do
  Typechecker { lvl, substs } <- get
  case Data.HashMap.lookup vi substs of
    Just t' -> generalise t'
    Nothing -> pure $ if vl > lvl then Type.QVar (pack $ "a" ++ show vi) else t
generalise (Type.Tuple ts) = Type.Tuple <$> mapM generalise ts
generalise (Type.Fun xs y) = Type.Fun <$> mapM generalise xs <*> generalise y
generalise (Type.Data i ts) = Type.Data i <$> mapM generalise ts
generalise t = pure t

instantiateL' :: [Type.Type] -> Map Text TypeVar -> StateT Typechecker Result ([Type.Type], Map Text TypeVar)
instantiateL' [] m = pure ([], m)
instantiateL' (x:xs) m = do
  (x', m) <- instantiate' x m
  (xs', m) <- instantiateL' xs m
  pure (x':xs, m)

instantiate' :: Type.Type -> Map Text TypeVar -> StateT Typechecker Result (Type.Type, Map Text TypeVar)
instantiate' (Type.QVar x) m = case Data.HashMap.lookup x m of
                                         Just v -> pure (Type.Variable v, m)
                                         Nothing -> do
                                           v <- newVar
                                           pure (Type.Variable v, insert x v m)
instantiate' t@(Type.Variable (vi, _)) m = do
          Typechecker { substs } <- get
          case Data.HashMap.lookup vi substs of
            Just t -> instantiate' t m
            Nothing -> pure (t, m)
instantiate' (Type.Tuple ts) m = map1 Type.Tuple <$> instantiateL' ts m
instantiate' (Type.Fun xs y) m = do
  (xs', m) <- instantiateL' xs m
  (y', m) <- instantiate' y m
  pure (Type.Fun xs' y', m)
instantiate' (Type.Data i ts) m = map1 (Type.Data i) <$> instantiateL' ts m
instantiate' t m = pure (t, m)

instantiate :: Type.Type -> StateT Typechecker Result Type.Type
instantiate t = fst <$> instantiate' t Data.HashMap.empty

tcExpr :: Expr.LocExprT -> StateT Typechecker Result Expr.LocExprT
tcExpr e@(Expr.Var (t, loc) x) = do
  Typechecker { bindings } <- get
  case Data.HashMap.lookup x bindings of
    Nothing -> throwError (loc, Unbound x)
    Just t' -> case t of
                 Nothing -> tcExpr $ Expr.Var (Just t', loc) x
                 Just t -> unify loc t t' >> pure e
tcExpr e@(Expr.Abs (t, loc) fargs expr) = do
  -- fresh type variables for arguments
  tfargs <- mapM (const $ Type.Variable <$> newVar) fargs
  -- unify type variables against the declared type of arguments
  let fargs' = Prelude.map (\((x, (t, loc)), t') -> (x, (Just $ t' `fromMaybe` t, loc))) $ Prelude.zip fargs tfargs
  mapM_ (\(t, (_, (t', loc))) -> unify loc t $ fromJust t') $ Prelude.zip tfargs fargs'
  tc@Typechecker { bindings } <- get
  let nb = Prelude.foldl (flip (\((x, _), t') -> insert x t')) bindings $ Prelude.zip fargs tfargs
  -- put the arguments in the environment
  put tc { bindings = nb }
  -- typecheck the return value in this context
  expr' <- tcExpr expr
  -- remove the arguments from the environment
  put tc { bindings }
  let t' = Type.Fun tfargs $ fromJust . fst . Expr.ann $ expr'
  case t of
    Nothing -> tcExpr $ Expr.Abs (Just t', loc) fargs' expr'
    Just t -> unify loc t t' >> pure e
