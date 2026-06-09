module Sefer.Typecheck ( Typechecker(..), TCError(..), initTC ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Foldable
import Data.HashMap
import Data.Tuple.Extra
import Data.Maybe
import Data.Text
import qualified Sefer.Expr as Expr
import Sefer.Location
import qualified Sefer.Type as Type
import qualified Data.List.Extra as Data.List
import Sefer.Type
import qualified Control.Exception as Type
import Sefer.Expr (Expr(fargs))
import Data.Traversable (for)
import Data.Functor

data Typechecker = Typechecker
                   {}
                   deriving Show

data TCError = NotSub Type Type
             | UndefTVar Int
             | UndefEVar Int
             | InfiniteType Int Type
             | IllFormed Type
             | NoArrowBind Int
             | NotInst Int Type
             deriving (Show, Eq)

type Result = Except (Located TCError)

initTC :: Typechecker
initTC =
  Typechecker

type Context = [CtxElem]

data CtxElem = CTVar Int
             | CBind Text Type
             | CEVar Int
             | CBVar Int Type
             | CMark Int
             deriving (Eq)

getBinding :: Int -> Context -> Maybe Type
getBinding _ [] = Nothing
getBinding i ((CBVar j t):_) | i == j = Just t
getBinding i (_:xs) = getBinding i xs

getVar :: Text -> Context -> Maybe Type
getVar x (CBind y t:xs) | x == y = Just t
getVar x (_:xs) = getVar x xs

wft :: Context -> Type -> Bool
wft ctx (Type.TVar i) = CTVar i `Prelude.elem` ctx
wft ctx (Type.Fun a b) = wft ctx a && wft ctx b
wft ctx (Type.Forall x t) = wft (CTVar x:ctx) t
wft ctx (Type.EVar i) = CEVar i `Prelude.elem` ctx || isJust (getBinding i ctx)
wft ctx (Type.Tuple ts) = Prelude.all (wft ctx) ts
wft _ _ = True

wfctx :: Context -> Bool
wfctx [] = True
wfctx (x@(CTVar _):xs) = wfctx xs && x `Prelude.notElem` xs
wfctx (x@(CEVar i):xs) = wfctx xs && x `Prelude.notElem` xs && isNothing (getBinding i xs)
wfctx (CBind x t:xs) = wfctx xs && isNothing (getVar x xs) && wft xs t
wfctx (CBVar i t:xs) = wfctx xs && wft xs t && CEVar i `Prelude.notElem` xs && isNothing (getBinding i xs)
wfctx (x@(CMark i):xs) = wfctx xs && x `Prelude.notElem` xs && CEVar i `Prelude.notElem` xs && isNothing (getBinding i xs)

subst :: Location -> Context -> Type -> Result Type
subst loc ctx (Type.Tuple ts) = Type.Tuple <$> mapM (subst loc ctx) ts
subst loc ctx (Type.Fun a b) = do
  sa <- subst loc ctx a
  sb <- subst loc ctx b
  pure $ Type.Fun sa sb
subst loc ctx (Type.Forall x t) = Type.Forall x <$> subst loc ctx t
subst loc ctx t@(Type.EVar i)
  | Just t' <- getBinding i ctx = subst loc ctx t'
  | CEVar i `Prelude.elem` ctx = pure t
  | otherwise = throwError (loc, UndefEVar i)
subst _ _ t = pure t

subst1 :: Type -> Type -> Type -> Type
subst1 a b t | t == b = a
subst1 a b (Type.Tuple as) = Type.Tuple $ Prelude.map (subst1 a b) as
subst1 a b (Type.Fun t u) = Type.Fun (subst1 a b t) (subst1 a b u)
subst1 a b (Type.Forall i t) | b /= Type.TVar i = Type.Forall i $ subst1 a b t
subst1 _ _ t = t

hole1 :: Context -> [CtxElem] -> Maybe (Context, Context)
hole1 xs [] = Just ([], xs)
hole1 (x:xs) (y:ys)
  | x == y = hole1 xs ys
  | otherwise = hole1 xs (y:ys) <&> first (x:)
hole1 [] _ = Nothing

hole2 :: Context -> ([CtxElem], [CtxElem]) -> Maybe (Context, Context, Context)
hole2 (x:xs) ([], y1) = hole1 (x:xs) y1 <&> \(xs, ys) -> ([], xs, ys)
hole2 (x:xs) (y0:y0s, y1)
  | x == y0 = hole2 xs (y0s, y1)
  | otherwise = hole2 xs (y0:y0s, y1) <&> first3 (x:)

subt :: Location -> Context -> Type -> Type -> Result Context
subt loc ctx (Type.TVar a) (Type.TVar b) | a == b = if isJust $ hole1 ctx [CTVar a] -- <:Var
                                                    then pure ctx
                                                    else throwError (loc, UndefTVar a)
subt loc ctx (Type.EVar a) (Type.EVar b) | a == b = if isJust $ hole1 ctx [CEVar a] -- <:Exvar
                                                    then pure ctx
                                                    else throwError (loc, UndefEVar a)
subt loc ctx Type.Character Type.Character = pure ctx -- <:Unit
subt loc ctx Type.Integer Type.Integer = pure ctx
subt loc ctx Type.Floating Type.Floating = pure ctx
subt loc ctx Type.Boolean Type.Boolean = pure ctx
subt loc ctx (Type.Tuple []) (Type.Tuple []) = pure ctx
subt loc ctx (Type.Tuple (a:as)) (Type.Tuple (b:bs)) = do
  ctx1 <- subt loc ctx a b
  a2' <- subst loc ctx1 (Type.Tuple as)
  b2' <- subst loc ctx1 (Type.Tuple bs)
  subt loc ctx1 a2' b2'
subt loc ctx (Type.Fun a1 a2) (Type.Fun b1 b2) = do -- <:->
  ctx1 <- subt loc ctx b1 a1
  a2' <- subst loc ctx1 a2
  b2' <- subst loc ctx1 b2
  subt loc ctx1 a2' b2'
subt loc ctx (Type.Forall i a) b = do-- <:∀L
  let a' = subst1 (Type.EVar i) (Type.TVar i) a
  ctx1 <- subt loc (CEVar i:(CMark i:ctx)) a' b
  pure . snd . fromJust $ hole1 ctx1 [CMark i]
subt loc ctx a (Type.Forall i b) = do -- <:∀R
  ctx1 <- subt loc (CTVar i:ctx) a b
  pure . snd . fromJust $ hole1 ctx1 [CTVar i]
subt loc ctx (Type.EVar i) a | isJust $ hole1 ctx [CEVar i] = do -- <:InstantiateL
  canInst loc i a
  instl loc ctx i a
subt loc ctx a (Type.EVar i) | isJust $ hole1 ctx [CEVar i] = do -- <:InstantiateR
  canInst loc i a
  instr loc ctx a i
subt loc _ a b = throwError (loc, NotSub a b)

canInst :: Location -> Int -> Type -> Result ()
canInst loc i t@(Type.EVar j) | i == j = throwError (loc, InfiniteType i t)
canInst loc i (Type.Tuple as) = mapM_ (canInst loc i) as
canInst loc i (Type.Fun a b) = canInst loc i a >> canInst loc i b
canInst _ _ _ = pure ()

checkWft :: Location -> Context -> Type -> Result ()
checkWft loc ctx t
  | wft ctx t = pure ()
  | otherwise = throwError (loc, IllFormed t)

getArrowBinding :: Location -> Context -> Int -> Result (Int, Int)
getArrowBinding loc [] i = throwError (loc, NoArrowBind i)
getArrowBinding _ ((CBVar i (Type.Fun (Type.EVar a) (Type.EVar b))):(CEVar k):(CEVar l):_) j | i == j && a == k && b == l = pure (a, b)
getArrowBinding loc (_:xs) i = getArrowBinding loc xs i

instl :: Location -> Context -> Int -> Type -> Result Context
instl loc ctx i t -- InstLSolve
  | Just (ctx1, ctx0) <- hole1 ctx [CEVar i] = do
      checkWft loc ctx0 t
      pure $ ctx1 ++ CBVar i t:ctx0
  | otherwise = throwError (loc, UndefEVar i)
instl loc ctx i (Type.EVar j) -- InstLReach
  | Just (ctx2, ctx1, ctx0) <- hole2 ctx ([CEVar j], [CEVar i]) = pure $ ctx2 ++ CBVar j (Type.EVar i):ctx1 ++ CEVar i:ctx0
  | isJust $ hole1 ctx [CEVar i] = throwError (loc, UndefEVar j)
  | otherwise = throwError (loc, UndefEVar i)
instl loc ctx i (Type.Fun a1 a2) | isJust $ hole1 ctx [CEVar i] = do -- InstLArr
  (i1, i2) <- getArrowBinding loc ctx i
  ctx1 <- instr loc ctx a1 i1
  a2' <- subst loc ctx1 a2
  instl loc ctx1 i2 a2'
instl loc ctx i (Type.Forall j b) | isJust $ hole1 ctx [CEVar i] = do -- InstLAIIR
  ctx1 <- instl loc (CTVar j:ctx) i b
  pure . snd . fromJust $ hole1 ctx1 [CTVar i]
instl loc _ i t = throwError (loc, NotInst i t)

instr :: Location -> Context -> Type -> Int -> Result Context
instr _ _ _ _ = error "TODO"
