{-# LANGUAGE NamedFieldPuns #-}
module Typecheck ( Typechecker(..), initTC ) where

import Control.Comonad.Cofree
import Control.Monad.State
import Data.HashMap
import Data.Maybe
import Data.Text
import Data.Tuple.Extra
import Expr
import Literal
import Statement
import Type

data Typechecker = Typechecker
                   { vg :: Int
                   , bindings :: Map Text Type0
                   , eqs :: [(Type0, Type0)]
                   , subst :: Map Type0 Type0
                   , scs :: [SumConstructor]
                   , adts :: [ADType]
                   }

data TCError = HeteroPrim Type0 Type0
               deriving (Show)

type Result = Either TCError

initTC :: [SumConstructor] -> [ADType] -> Typechecker
initTC scs adts = Typechecker { vg = 0
                              , bindings = Data.HashMap.empty
                              , eqs = []
                              , subst = Data.HashMap.empty
                              , scs
                              , adts
                              }

newVar :: State Typechecker Int
newVar = do
  tc@Typechecker { vg = x } <- get
  put tc { vg = x + 1 }
  pure x

addEq :: Type0 -> Type0 -> State Typechecker ()
addEq x y = do
  tc@Typechecker { eqs } <- get
  put tc { eqs = (x,y):eqs }
  pure ()

unify :: State Typechecker (Result ())
unify = pure $ Right () -- TODO

applySubsts :: LocExprTP0 -> State Typechecker LocExprTP0
applySubsts = pure -- TODO

extractType :: LocExprTP0 -> Type0
extractType ((Just t, _) :< _) = t

synth :: LocExprTP0 -> State Typechecker LocExprTP0
synth ((Nothing, loc) :< Literal l) = pure $ ((Just . getType0) l, loc) :< Literal l
synth ((Nothing, loc) :< Expr.Tuple el) = do
  ela <- mapM synth el
  let targs = Prelude.map (\((t, _) :< _) -> fromJust t) ela
  pure $ (Just $ Type.Tuple targs, loc) :< Expr.Tuple ela
synth ((Nothing, loc) :< Expr.App ((Nothing, loc1) :< Expr.Abs fargs expr) cargs) = do
  ctargs <- mapM synth cargs
  let f = (Nothing, loc1) :< Expr.Abs fargs expr
  ft <- synth f
  let ((tf, _) :< Expr.Abs ftargs _) = ft
  -- (\xyz -> e) a b c |- t(x) = t(a), t(y) = t(b), t(z) = t(c)
  mapM_ (uncurry addEq)
    $ Prelude.zipWith (curry . both $ extractType) ftargs ctargs
  pure $ (tf, loc) :< Expr.App ft ctargs
synth ((Nothing, loc) :< Expr.Abs fargs expr) = do
  exprt <- synth expr
  ftargs <- mapM synth fargs
  pure $ (Just $ Type.Fun (Prelude.map extractType ftargs) $ extractType exprt, loc)
         :< Expr.Abs ftargs exprt
synth ((Nothing, loc) :< Expr.Const i args) = do
  argst <- mapM synth args
  tc@Typechecker { scs, adts } <- get
  let k = scs !! i
  let adt = adts !! parent k
  let targs = Prelude.drop (nVar adt) . Prelude.map extractType $ argst
  pure $ (Just $ Data (parent k) targs, loc) :< Expr.Const i argst
synth ((Nothing, loc) :< Expr.Let x y z) = do
  xt <- synth x
  yt <- synth y
  zt <- synth z
  addEq (extractType xt) (extractType yt)
  pure $ (Just . extractType $ zt, loc) :< Expr.Let xt yt zt
synth ((Nothing, loc) :< Expr.Cond ei et ee) = do
  eit <- synth ei
  ett <- synth et
  eet <- synth ee
  addEq (extractType ett) (extractType eet)
  addEq (extractType eit) Type.Boolean
  pure $ (Just . extractType $ ett, loc) :< Expr.Cond eit ett eet
synth ((Nothing, loc) :< Expr.Match e ps) = do
  et <- synth e
  pst <- mapM (\(bp, bc, be) -> (,,) bp <$> synth bc <*> synth be) ps
  let pt = Prelude.map (extractType . thd3) pst
  mapM_ (uncurry addEq) $ pairs pt 
  pure $ (Just . Prelude.head $ pt, loc) :< Expr.Match et pst
synth ((Nothing, loc) :< e) = do
  i <- newVar
  pure $ (Just $ Type.Variable i, loc) :< e
synth x =  pure x -- already typed

check :: LocExprTP0 -> Type0 -> State Typechecker (Result ())
check _ _ = unify -- TODO
-- TODO: check pattern homogeneity

pairs :: [a] -> [(a, a)]
pairs [] = []
pairs (x:xs) = let mkp = (,) x
               in Prelude.map mkp xs ++ pairs xs
