{-# LANGUAGE NamedFieldPuns #-}
module Typecheck ( Typechecker(..), initTC ) where

import Control.Monad.Except
import Control.Comonad.Cofree
import Control.Monad.State
import Data.HashMap
import Data.Maybe
import Data.Text
import Data.Tuple.Extra
import Expr
import Literal
import Location
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
             | Unbound Text
             deriving (Show)

type Result = Either (Located TCError)

initTC :: [SumConstructor] -> [ADType] -> Typechecker
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

unify :: StateT Typechecker Result ()
unify = pure () -- TODO

applySubsts :: LocExprTP0 -> StateT Typechecker Result LocExprTP0
applySubsts = pure -- TODO

extractType :: LocExprTP0 -> Type0
extractType ((Just t, _) :< _) = t

addEqBind :: Text -> Type0 -> Type0 -> StateT Typechecker Result ()
addEqBind x tx ty = do
  addEq tx ty
  tc@Typechecker { bindings } <- get
  put tc { bindings = Data.HashMap.insert x tx bindings }
  pure ()

getBindingTypes ((Just t, _) :< Expr.Binding x) ((Just u, _) :< _) = (x, t, u)

synth :: LocExprTP0 -> StateT Typechecker Result LocExprTP0
synth ((Nothing, loc) :< Literal l) = pure $ ((Just . getType0) l, loc) :< Literal l
synth ((Nothing, loc) :< Expr.Tuple el) = do
  ela <- mapM synth el
  let targs = Prelude.map extractType ela
  pure $ (Just $ Type.Tuple targs, loc) :< Expr.Tuple ela
synth ((Nothing, loc) :< Expr.App ((tf, loc1) :< Expr.Abs fargs expr) cargs) = do
  ctargs <- mapM synth cargs
  let f = (tf, loc1) :< Expr.Abs fargs expr
  ft <- synth f
  let ((tf, _) :< Expr.Abs ftargs _) = ft
  -- (\xyz -> e) a b c |- t(x) = t(a), t(y) = t(b), t(z) = t(c)
  tc@Typechecker { bindings } <- get
  mapM_ (uncurry3 addEqBind)
    $ Prelude.zipWith getBindingTypes ftargs ctargs
  put tc { bindings }
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
  let (Just tx, _) :< Expr.Binding xb = xt
  addEq tx (extractType yt)
  tc@Typechecker { bindings } <- get
  let nb = Data.HashMap.insert xb tx bindings
  put tc { bindings = nb }
  zt <- synth z
  tc <- get
  put tc { bindings }
  pure $ (Just . extractType $ zt, loc) :< Expr.Let xt yt zt
synth ((Nothing, loc) :< Expr.Cond ei et ee) = do
  eit <- synth ei
  ett <- synth et
  eet <- synth ee
  addEq (extractType ett) (extractType eet)
  addEq (extractType eit) Type.Boolean
  pure $ (Just . extractType $ ett, loc) :< Expr.Cond eit ett eet
synth ((Nothing, loc) :< Expr.Binding x) = do
  i <- newVar
  pure $ (Just $ Type.Variable i, loc) :< Expr.Binding x
synth ((Nothing, loc) :< Expr.Var x) = do
  tc@Typechecker { bindings } <- get
  case Data.HashMap.lookup x bindings of
    Nothing -> throwError (loc, Unbound x)
    Just t -> pure $ (Just t, loc) :< Expr.Var x
synth x =  pure x -- already typed

check :: LocExprTP0 -> Type0 -> StateT Typechecker Result ()
check _ _ = unify -- TODO

pairs :: [a] -> [(a, a)]
pairs [] = []
pairs (x:xs) = let mkp = (,) x
               in Prelude.map mkp xs ++ pairs xs
