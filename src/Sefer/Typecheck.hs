{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
module Sefer.Typecheck ( Typechecker(..), TCError(..), initTC, runTC ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Foldable
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

data Typechecker = Typechecker
                   { vg :: Int
                   , bindings :: Map Text Type.Type
                   , eqs :: [(Type.Type, Type.Type)]
                   , subst :: Map Int Type.Type
                   , scs :: [Constructor]
                   , adts :: [ADType]
                   }
                   deriving Show

data TCError = HeteroPrim Type.Type Type.Type
             | Unbound Text
             | TupleArity Int Int
             | FunArity Int Int
             | CallArity Int Int
             | ConstArity Int Int
             | WrongADT Int Int
             | UnifyFail Type.Type Type.Type
             | InfiniteType Type.Type Type.Type
             | MissingAnnotations Expr.LocExprT Expr.LocExprT Int
             deriving (Show, Eq)

type Result = Either (Located TCError)

initTC :: [Constructor] -> [ADType] -> Typechecker
initTC scs adts = Typechecker { vg = 0
                              , bindings = defaultBindings
                              , eqs = []
                              , subst = Data.HashMap.empty
                              , scs
                              , adts
                              }

undecidedT ::  Type.Type -> Maybe Int
undecidedT (Type.Variable i) = Just i
undecidedT (Type.Tuple ts) = asum . Prelude.map undecidedT $ ts
undecidedT (Type.Fun ts tr) = asum . Prelude.map undecidedT $ tr:ts
undecidedT (Type.Data _ ts) = asum . Prelude.map undecidedT $ ts
undecidedT _ = Nothing

undecidedP' :: Pattern.LocPatternT -> Maybe Int
undecidedP' (Pattern.Tuple _ xs) = asum .Prelude.map undecidedP $ xs
undecidedP' (Pattern.Const _ _ xs) = asum . Prelude.map undecidedP $ xs
undecidedP' (Pattern.Or _ lp rp) = undecidedP lp <|> undecidedP rp
undecidedP' (Pattern.At _ _ p) = undecidedP p
undecidedP' _ = Nothing

undecidedP :: Pattern.LocPatternT -> Maybe Int
undecidedP p = (undecidedT =<< (fst . Pattern.ann $ p)) <|> undecidedP' p

undecidedB :: Expr.LocBranchT -> Maybe Int
undecidedB (Expr.Branch (t, _) p g b) = (t >>= undecidedT)
                                      <|> undecidedP p
                                      <|> (snd <$> (g >>= undecided))
                                      <|> (snd <$> undecided b)

undecided' :: Expr.LocExprT -> Maybe (Expr.LocExprT, Int)
undecided' (Expr.Tuple _ xs) = asum . Prelude.map undecided $ xs
undecided' (Expr.Const _ _ xs) = asum . Prelude.map undecided $ xs
undecided' (Expr.App _ f as) = asum . Prelude.map undecided $ f:as
undecided' e@(Expr.Abs _ as e') = undecided e' <|> (asum . flip Prelude.map as $ ((,) e <$>) . (=<<) undecidedT . fst . snd)
undecided' e@(Expr.Let _ (_, (ta, _)) y z) = (,) e <$>  (undecidedT =<< ta) <|> undecided y <|> undecided z
undecided' (Expr.Cond _ ei et ee) = undecided ei <|> undecided et <|> undecided ee
undecided' (Expr.Match _ e bs) = undecided e <|> (,) e <$> (asum . Prelude.map undecidedB) bs
undecided' _ = Nothing

undecided :: Expr.LocExprT -> Maybe (Expr.LocExprT, Int)
undecided e = (((,) e <$>) . (=<<) undecidedT . fst . Expr.ann $ e) <|> undecided' e

runTC :: Expr.LocExprT -> StateT Typechecker Result Expr.LocExprT
runTC e = do
  e' <- tcExpr e >>= applySubstsL
  case undecided e' of
    Nothing -> pure e'
    Just (e'', i) -> throwError (snd . Expr.ann $ e', MissingAnnotations e' e'' i)

defaultBindings :: Map Text Type.Type
defaultBindings = Data.HashMap.fromList [ (pack "$addInt", Type.Fun [Type.Integer, Type.Integer] Type.Integer)
                                        , (pack "$id", Type.Fun [Type.RVar $ pack "a"] $ Type.RVar $ pack "a")
                                        , (pack "$const", Type.Fun [Type.RVar $ pack "a", Type.RVar $ pack "b"]
                                                          $ Type.RVar $ pack "a")
                                        ]

newVar :: StateT Typechecker Result Int
newVar = do
  tc@Typechecker { vg = x } <- get
  put tc { vg = x + 1 }
  pure x

addEq :: Location -> Type.Type -> Type.Type -> StateT Typechecker Result ()
addEq loc x y | x == y = pure ()
              | otherwise = if occurs x y || occurs y x
                            then throwError (loc, InfiniteType x y)
                            else do
                  tc@Typechecker { eqs } <- get
                  put tc { eqs = (x,y):eqs }

occurs :: Type.Type -> Type.Type -> Bool
occurs x y | x == y = True
occurs x (Type.Tuple ys) = flip Prelude.any ys $ occurs x
occurs x (Type.Fun ts tr) = flip Prelude.any (tr:ts) $ occurs x
occurs x (Type.Data _ ts) = flip Prelude.any ts $ occurs x
occurs _ _ = False

substEq :: [(Type.Type, Type.Type)] -> Map Int Type.Type -> [(Type.Type, Type.Type)]
substEq [] _ = []
substEq (x:xs) m = Data.List.snoc (substEq xs m) $ both (applySubstsT m) x

unifyLists :: Location -> [Type.Type] -> [Type.Type] -> [(Type.Type, Type.Type)] -> StateT Typechecker Result ([(Type.Type, Type.Type)], Map Int Type.Type)
unifyLists loc ls rs xs = do
  (eq, ss) <- unifyList loc $ Prelude.zip ls rs
  let eq' = substEq eq ss
  let xs' = substEq xs ss
  (eq1, ss1) <- unifyList loc xs'
  let eq1' = flip substEq ss1 $ eq' ++ eq1
  pure (eq1', Data.HashMap.union ss1 ss)

unifyList :: Location -> [(Type.Type, Type.Type)] -> StateT Typechecker Result ([(Type.Type, Type.Type)], Map Int Type.Type)
unifyList _ [] = pure ([], Data.HashMap.empty)
unifyList _ ((Type.RVar _, _):_) = error "not supposed to encounter strict typevars in unify"
unifyList _ ((_, Type.RVar _):_) = error "not supposed to encounter strict typevars in unify"
unifyList loc ((Type.Variable i, Type.Variable j):xs) | i == j = unifyList loc xs
unifyList loc ((Type.Variable i, t):xs) = do
  let sub = Data.HashMap.singleton i t
  let xs' = substEq xs sub
  (eq, ss) <- unifyList loc xs'
  let ss' = Data.HashMap.union ss sub
  let eq' = substEq eq ss'
  pure (eq', ss')
unifyList loc ((t, Type.Variable i):xs) = do
  let sub = Data.HashMap.singleton i t
  let xs' = substEq xs sub
  (eq, ss) <- unifyList loc xs'
  let ss' = Data.HashMap.union ss sub
  let eq' = substEq eq ss'
  pure (eq', ss')
unifyList loc ((Type.Fun largs lr, Type.Fun rargs rr):xs) = unifyLists loc (lr:largs) (rr:rargs) xs
unifyList loc ((Type.Data li largs, Type.Data ri rargs):xs)
  | li == ri = unifyLists loc largs rargs xs
  | otherwise = throwError (loc, WrongADT li ri)
unifyList loc ((lht, rht):xs) | lht == rht = unifyList loc xs
                              | otherwise = throwError (loc, UnifyFail lht rht)

unify :: Location -> StateT Typechecker Result ()
unify loc = do
  tc@Typechecker { eqs, subst } <- get
  let eqs' = substEq eqs subst
  (eqs, subst') <- unifyList loc eqs'
  put tc { eqs, subst = Data.HashMap.union subst' subst }

applySubstsL :: Expr.LocExprT -> StateT Typechecker Result Expr.LocExprT
applySubstsL e = do
  Typechecker { subst } <- get
  let e' = applySubsts subst e
  if e == e' then pure e else applySubstsL e'

-- TODO: rewrite all similar functions as calls to a more general function
applySubstsB :: Map Int Type.Type -> Expr.LocBranchT -> Expr.Branch (Maybe Type.Type, Location)
applySubstsB m (Expr.Branch (t, loc) pat grd bdy) = let pat' = applySubstsP m pat
                                                        grd' = applySubsts m <$> grd
                                                        bdy' = applySubsts m bdy
                                                      in Expr.Branch (applySubstsT m <$> t, loc) pat' grd' bdy'

applySubstsP' :: Type.LocAnnT -> Map Int Type.Type -> Pattern.LocPatternT -> Pattern.LocPatternT
applySubstsP' st m (Pattern.Literal _ lit) = Pattern.Literal st lit
applySubstsP' st m (Pattern.Tuple _ args) = Pattern.Tuple st $ flip Prelude.map args $ applySubstsP m
applySubstsP' st m (Pattern.Binding _ v) = Pattern.Binding st v
applySubstsP' st m (Pattern.Const _ k cargs) = Pattern.Const st k $ flip Prelude.map cargs $ applySubstsP m
applySubstsP' st m (Pattern.Or _ lp rp) = Pattern.Or st (applySubstsP m lp) (applySubstsP m rp)
applySubstsP' st m (Pattern.At _ v p) = Pattern.At st v $ applySubstsP m p

applySubstsP :: Map Int Type.Type -> Pattern.LocPatternT -> Pattern.LocPatternT
applySubstsP m p = case Pattern.ann p of
                       (Just t, loc) -> applySubstsP' (Just $ applySubstsT m t, loc) m p
                       (Nothing, loc) -> applySubstsP' (Nothing, loc) m p

applySubstsT :: Map Int Type.Type -> Type.Type -> Type.Type
applySubstsT m (Type.Variable j) = case Data.HashMap.lookup j m of
                                    Nothing -> Type.Variable j
                                    Just t -> t
applySubstsT m (Type.Tuple ts) = Type.Tuple $ flip Prelude.map ts $ applySubstsT m
applySubstsT m (Type.Fun args et) = flip Type.Fun (applySubstsT m et) $ flip Prelude.map args $ applySubstsT m
applySubstsT m (Type.Data d ts) = Type.Data d $ flip Prelude.map ts $ applySubstsT m
applySubstsT _ t = t

applySubsts' :: Type.LocAnnT -> Map Int Type.Type -> Expr.LocExprT -> Expr.LocExprT
applySubsts' st _ (Expr.Literal _ lit) = Expr.Literal st lit
applySubsts' st m (Expr.Tuple _ args) = Expr.Tuple st $ flip Prelude.map args $ applySubsts m
applySubsts' st _ (Expr.Var _ v) = Expr.Var st v
applySubsts' st m (Expr.Const _ k args) = Expr.Const st k $ flip Prelude.map args $ applySubsts m
applySubsts' st m (Expr.App _ f args) = Expr.App st (applySubsts m f) $ flip Prelude.map args $ applySubsts m
applySubsts' st m (Expr.Abs _ args e) = flip (Expr.Abs st) (applySubsts m e) $ flip Prelude.map args $ \(x, (tx, xl)) -> (x, (applySubstsT m <$> tx, xl))
applySubsts' st m (Expr.Let _ (x, (tx, xl)) y z) =  Expr.Let st (x, (applySubstsT m <$> tx, xl)) (applySubsts m y) (applySubsts m z)
applySubsts' st m (Expr.Cond _ x y z) = Expr.Cond st (applySubsts m x) (applySubsts m y) (applySubsts m z)
applySubsts' st m (Expr.Match _ e bs) = Expr.Match st (applySubsts m e) $ flip Prelude.map bs $ applySubstsB m

applySubsts :: Map Int Type.Type -> Expr.LocExprT -> Expr.LocExprT
applySubsts m e = case Expr.ann e of
                      (Just t, loc) -> applySubsts' (Just $ applySubstsT m t, loc) m e
                      (Nothing, loc) -> applySubsts' (Nothing, loc) m e

extractType :: Expr.LocExprT -> Type.Type
extractType e = case Expr.ann e of
                  (Just t, _) -> t

extractTypeP :: Pattern.LocPatternT -> Type.Type
extractTypeP p = case Pattern.ann p of
                   (Just t, _) -> t

checkLists :: Location -> [Type.Type] -> [Type.Type] -> StateT Typechecker Result ()
checkLists loc (x:xs) (y:ys) = addEq loc x y >> checkLists loc xs ys
-- works for curried applications:
-- f : a -> b -> c, x : a => f x : b -> c
-- checkLists _ [a b] [a] -> checkLists _ [b] []
checkLists loc _ [] = unify loc

instanciateP' :: Type.LocAnnT -> Map Text Type.Type -> Pattern.LocPatternT -> Pattern.LocPatternT
instanciateP' it m (Pattern.Literal _ lit) = Pattern.Literal it lit
instanciateP' it m (Pattern.Tuple _ args) = Pattern.Tuple it $ flip Prelude.map args $ instanciateP m
instanciateP' it m (Pattern.Binding _ x) = Pattern.Binding it x
instanciateP' it m (Pattern.Const _ i args) = Pattern.Const it i $ flip Prelude.map args $ instanciateP m
instanciateP' it m (Pattern.Or _ lp rp) = Pattern.Or it (instanciateP m lp) (instanciateP m rp)
instanciateP' it m (Pattern.At _ x p) = Pattern.At it x (instanciateP m p)

instanciateP :: Map Text Type.Type -> Pattern.LocPatternT -> Pattern.LocPatternT
instanciateP m p = case Pattern.ann p of
                     (Just t, loc) -> instanciateP' (Just $ instanciateT m t, loc) m p
                     (Nothing, loc) -> instanciateP' (Nothing, loc) m p

instanciateB :: Map Text Type.Type -> Expr.LocBranchT -> Expr.LocBranchT
instanciateB m (Expr.Branch (t, loc) p g e) = Expr.Branch (instanciateT m <$> t, loc)
                                              (instanciateP m p)
                                              (instanciate m <$> g)
                                              (instanciate m e)

instanciate' :: Type.LocAnnT -> Map Text Type.Type -> Expr.LocExprT -> Expr.LocExprT
instanciate' it _ (Expr.Literal _ lit) = Expr.Literal it lit
instanciate' it m (Expr.Tuple _ args) = Expr.Tuple it $ flip Prelude.map args $ instanciate m
instanciate' it _ (Expr.Var _ v) = Expr.Var it v
instanciate' it m (Expr.Const _ k args) = Expr.Const it k $ flip Prelude.map args $ instanciate m
instanciate' it m (Expr.App _ f args) = Expr.App it (instanciate m f) $ flip Prelude.map args $ instanciate m
instanciate' it m (Expr.Abs _ args e) = flip (Expr.Abs it) (instanciate m e) $ flip Prelude.map args $ \(x, (tx, xl)) -> (x, (instanciateT m <$> tx, xl))
instanciate' it m (Expr.Let _ (x, (tx, xl)) y z) = Expr.Let it (x, (instanciateT m <$> tx, xl)) (instanciate m y) (instanciate m z)
instanciate' it m (Expr.Cond _ ei et ee) = Expr.Cond it (instanciate m ei) (instanciate m et) (instanciate m ee)
instanciate' it m (Expr.Match _ e bs) = Expr.Match it (instanciate m e) $ flip Prelude.map bs $ instanciateB m

instanciate :: Map Text Type.Type -> Expr.LocExprT -> Expr.LocExprT
instanciate m e = case Expr.ann e of
                    (Nothing, loc) -> instanciate' (Nothing, loc) m e
                    (Just t, loc) -> instanciate' (Just $ instanciateT m t, loc) m e

instanciateT :: Map Text Type.Type -> Type.Type -> Type.Type
instanciateT m t@(Type.RVar x) = fromMaybe t $ Data.HashMap.lookup x m
instanciateT m (Type.Tuple ts) = Type.Tuple $ flip Prelude.map ts $ instanciateT m
instanciateT m (Type.Fun ts tr) = flip Type.Fun (instanciateT m tr) $ flip Prelude.map ts $ instanciateT m
instanciateT m (Type.Data i ts) = Type.Data i $ flip Prelude.map ts $ instanciateT m
instanciateT _ t = t

getTVarInstances :: [Type.Type] -> [Type.Type] -> Map Text Type.Type
getTVarInstances xs ys = Data.HashMap.fromList . flip Data.Maybe.mapMaybe (Prelude.zip xs ys) $ \case { (Type.RVar v, t) -> Just (v, t); _ -> Nothing }

unifyADTArgs :: Location -> [Type.Type] -> [Type.Type] -> Map Text Type.Type -> StateT Typechecker Result (Map Text Type.Type)
unifyADTArgs _ [] [] m = pure m
unifyADTArgs loc [] ts _ = throwError (loc, ConstArity 0 $ Prelude.length ts)
unifyADTArgs loc ks [] _ = throwError (loc, flip ConstArity 0 $ Prelude.length ks)
unifyADTArgs loc (Type.Character:ks) (Type.Character:ts) m = unifyADTArgs loc ks ts m
unifyADTArgs loc (Type.Integer:ks) (Type.Integer:ts) m = unifyADTArgs loc ks ts m
unifyADTArgs loc (Type.Floating:ks) (Type.Floating:ts) m = unifyADTArgs loc ks ts m
unifyADTArgs loc (Type.Boolean:ks) (Type.Boolean:ts) m = unifyADTArgs loc ks ts m
unifyADTArgs loc ((Type.Tuple k):ks) ((Type.Tuple t):ts) m = unifyADTArgs loc k t m >>= unifyADTArgs loc ks ts
unifyADTArgs loc ((Type.RVar x):ks) (t:ts) m = (if Data.HashMap.findWithDefault t x m == t
                                               then pure $ insert x t m
                                               else throwError (loc, flip UnifyFail t $ m ! x))
                                              >>= unifyADTArgs loc ks ts
unifyADTArgs _ ((Type.Variable _):_) _ _ = error "shouldn't see type variables on the left hand side"
unifyADTArgs loc (k:ks) (t@(Type.Variable _):ts) m = do
  addEq loc k t -- is that enough?
  unify loc
  unifyADTArgs loc ks ts m
unifyADTArgs loc ((Type.Fun xs e):ks) ((Type.Fun xs' e'):ts) m = unifyADTArgs loc [e] [e'] m
                                                                 >>= unifyADTArgs loc xs xs'
                                                                 >>= unifyADTArgs loc ks ts
unifyADTArgs loc ((Type.Data i xs):ks) ((Type.Data j xs'):ts) m = if i == j
                                                                  then unifyADTArgs loc xs xs' m
                                                                       >>= unifyADTArgs loc ks ts
                                                                  else throwError (loc, WrongADT i j)
unifyADTArgs loc (k:_) (t:_) _ = throwError (loc, HeteroPrim k t)

tcExpr :: Expr.LocExprT -> StateT Typechecker Result Expr.LocExprT
tcExpr e@(Expr.Literal (t, loc) l) = let tt = Literal.getType l
                                in case t of
                                     Nothing -> tcExpr $ Expr.Literal (Just tt, loc) l
                                     Just (Type.Variable i) -> do
                                       addEq loc (Type.Variable i) tt
                                       unify loc
                                       pure e
                                     Just t | t == tt -> pure e
                                            | otherwise -> throwError (loc, HeteroPrim t tt)
tcExpr (Expr.Tuple (t, loc) el) = do
  ela <- mapM tcExpr el
  let targs = Prelude.map extractType ela
  case t of
    Nothing -> tcExpr $ Expr.Tuple (Just $ Type.Tuple targs, loc) ela
    Just (Type.Variable i) -> do
      addEq loc (Type.Variable i) (Type.Tuple targs)
      unify loc
      pure $ Expr.Tuple (t, loc) ela
    Just (Type.Tuple targs1) -> do
      if Prelude.length targs /= Prelude.length targs1
      then throwError (loc, TupleArity (Prelude.length targs1) (Prelude.length targs))
      else checkLists loc targs targs1
      pure $ Expr.Tuple (Just $ Type.Tuple targs, loc) ela
    Just t -> throwError (loc, HeteroPrim t $ Type.Tuple targs)
tcExpr (Expr.App (t, loc) (Expr.Abs (tf, loc1) fargs expr) cargs) = do
  ctargs <- mapM tcExpr cargs
  let f = Expr.Abs (tf, loc1) fargs expr
  ft <- tcExpr f
  let (Expr.Abs _ ftargs exprt) = ft
  -- (\xyz -> e) a b c |- t(x) = t(a), t(y) = t(b), t(z) = t(c)
  let targs = Prelude.map (fromJust . fst . snd) ftargs
  let tcargs = Prelude.map extractType ctargs
  if Prelude.length targs < Prelude.length tcargs
    then throwError (loc, CallArity (Prelude.length targs) (Prelude.length tcargs))
    else checkLists loc targs tcargs -- unifies
  let htargs = Prelude.drop (Prelude.length tcargs) targs
  let te = extractType exprt
  let tapp = if Prelude.null htargs
             then te
             else Type.Fun htargs te
  case t of
    Nothing -> tcExpr $ Expr.App (Just tapp, loc) ft ctargs
    Just t -> do
      addEq loc t tapp
      unify loc
      pure $ Expr.App (Just t, loc) ft ctargs
tcExpr (Expr.App (t, loc) f cargs) = do
  ctargs <- mapM tcExpr cargs
  ft <- tcExpr f
  tr <- case extractType ft of
    Type.Fun targs tr -> do
      if Prelude.length targs < Prelude.length ctargs
        then throwError (loc, FunArity (Prelude.length targs) (Prelude.length ctargs))
        else checkLists loc targs $ Prelude.map extractType ctargs -- unifies
      let htargs = Prelude.drop (Prelude.length ctargs) targs
      if Prelude.null htargs
        then pure tr
        else pure $ Type.Fun htargs tr
    Type.Variable i -> do
      tr <- Type.Variable <$> newVar
      addEq loc (Type.Variable i) $ flip Type.Fun tr $ Prelude.map extractType ctargs
      pure tr
    t -> newVar >>= \i -> throwError (loc, HeteroPrim t $ flip Type.Fun (Type.Variable i) $ Prelude.map extractType ctargs)
  case t of
    Nothing -> tcExpr $ Expr.App (Just tr, loc) ft ctargs
    Just t -> do
      addEq loc t tr
      unify loc
      pure $ Expr.App (Just t, loc) ft ctargs
tcExpr (Expr.Abs (t, loc) fargs expr) = do
  ftargs <- mapM tcBind fargs
  let targs = Prelude.map (fst . snd) ftargs
  tc@Typechecker { bindings } <- get
  let nb = flip Data.HashMap.union bindings $ Data.HashMap.fromList $ Prelude.map (\(x, (t, _)) -> (x, t)) ftargs
  put tc { bindings = nb }
  exprt <- tcExpr expr
  tc <- get
  put tc { bindings }
  let tr = extractType exprt
  let te = Type.Fun targs tr
  let ttargs = flip Prelude.map ftargs $ \(x, (t, l)) -> (x, (Just t, l))
  case t of
    Nothing -> tcExpr $ Expr.Abs (Just te, loc) ttargs exprt
    Just (Type.Fun targs1 tr1) -> do
      if Prelude.length targs /= Prelude.length targs1
        then throwError (loc, FunArity (Prelude.length targs1) (Prelude.length targs))
        else do
        addEq loc tr tr1
        checkLists loc targs targs1 -- unifies
        pure $ Expr.Abs (t, loc) ttargs exprt
    Just (Type.Variable i) -> do
      addEq loc (Type.Variable i) te
      unify loc
      pure $ Expr.Abs (t, loc) ttargs exprt
    Just t -> throwError (loc, HeteroPrim t te)
tcExpr (Expr.Const (t, loc) i args) = do
  argst <- mapM tcExpr args
  Typechecker { scs, adts } <- get
  let k = scs !! i
  let ktargs = targs k
  let adt = adts !! parent k
  targsm <- unifyADTArgs loc ktargs (Prelude.map extractType argst) Data.HashMap.empty
  targs <- mapM (\t -> case Data.HashMap.lookup t targsm of
                         Nothing -> Type.Variable <$> newVar
                         Just t -> pure t) $ vars adt
  let tk = Type.Data (parent k) targs
  case t of
    Nothing -> tcExpr $ Expr.Const (Just tk, loc) i argst
    Just (Type.Data ti targs1) -> if parent k /= ti
                                  then throwError (loc, WrongADT ti (parent k))
                                  else do
      checkLists loc targs targs1 -- unifies
      pure $ Expr.Const (t, loc) i argst
    Just (Type.Variable j) -> do
      addEq loc (Type.Variable j) tk
      unify loc
      pure $ Expr.Const (t, loc) i argst
    Just t -> throwError (loc, HeteroPrim t tk)
tcExpr (Expr.Let (t, loc) x y z) = do
  (xt, (tx, xl)) <- tcBind x
  yt <- tcExpr y
  addEq loc tx (extractType yt)
  unify loc
  tc@Typechecker { bindings } <- get
  let nb = Data.HashMap.insert xt tx bindings
  put tc { bindings = nb }
  zt <- tcExpr z
  tc <- get
  put tc { bindings }
  let tz = extractType zt
  case t of
    Nothing -> tcExpr $ Expr.Let (Just tz, loc) (xt, (Just tx, xl)) yt zt
    Just t -> do
      addEq loc t tz
      unify loc
      pure $ Expr.Let (Just t, loc) (xt, (Just tx, xl)) yt zt
tcExpr (Expr.Cond (t, loc) ei et ee) = do
  eit <- tcExpr ei
  ett <- tcExpr et
  eet <- tcExpr ee
  addEq loc (extractType ett) (extractType eet)
  addEq loc (extractType eit) Type.Boolean
  unify loc
  case t of
    Nothing -> tcExpr $ Expr.Cond (Just . extractType $ ett, loc) eit ett eet
    Just t -> do
      addEq loc t (extractType ett)
      unify loc
      pure $ Expr.Cond (Just t, loc) eit ett eet
tcExpr e@(Expr.Var (t0, loc) x) = do
  Typechecker { bindings } <- get
  case Data.HashMap.lookup x bindings of
    Nothing -> throwError (loc, Unbound x)
    Just t1 -> case t0 of
                 Nothing -> tcExpr $ Expr.Var (Just t1, loc) x
                 Just t0 -> do
                   addEq loc t0 t1
                   unify loc
                   pure e
tcExpr (Expr.Match (t, loc) e bs) = do
  et <- tcExpr e
  bst <- forM bs $ tcBranch et
  mapM_ (uncurry $ addEq loc) $ pairs $ flip Prelude.map bst $ extractType . \(Expr.Branch _ _ _ b) -> b
  unify loc
  let tr = (\(Expr.Branch (Just t, _) _ _ _) -> t) $ Prelude.head bst
  case t of
    Nothing -> tcExpr $ Expr.Match (Just tr, loc) et bst
    Just t -> do
      addEq loc t tr
      unify loc
      pure $ Expr.Match (Just t, loc) et bst

tcBranch :: Expr.LocExprT -> Expr.LocBranchT -> StateT Typechecker Result Expr.LocBranchT
tcBranch et (Expr.Branch (t, loc) pat grd bdy) = do
  pt <- tcPattern pat
  addEq loc (extractType et) (extractTypeP pt)
  unify loc
  tc@Typechecker { bindings } <- get
  bnd <- fetchBindings pt
  let nb = flip Data.HashMap.union bindings $ Data.HashMap.fromList $ bnd
  put tc { bindings = nb }
  gt <- traverse tcExpr grd
  bt <- tcExpr bdy
  tc <- get
  put tc { bindings = nb }
  for_ gt $ addEq loc Type.Boolean . extractType
  unify loc
  case t of
    Nothing -> tcBranch et $ Expr.Branch (Just $ extractType bt, loc) pt gt bt
    Just t -> do
      addEq loc t (extractType bt)
      unify loc
      pure $ Expr.Branch (Just t, loc) pt gt bt

fetchBindings :: Pattern.LocPatternT -> StateT Typechecker Result [(Text, Type.Type)]
fetchBindings (Pattern.Tuple _ el) = Prelude.concat <$> mapM fetchBindings el
fetchBindings (Pattern.Binding (Just t, _) x) = pure [(x, t)]
fetchBindings (Pattern.Const _ _ cargs) = Prelude.concat <$> mapM fetchBindings cargs
fetchBindings (Pattern.Or (_, loc) lp rp) = do
  lb <- fetchBindings lp
  rb <- fetchBindings rp
  checkHomogeneity loc lb rb
  pure $ lb ++ rb
  where checkHomogeneity :: Location -> [(Text, Type.Type)] -> [(Text, Type.Type)] -> StateT Typechecker Result ()
        checkHomogeneity _ _ [] = pure ()
        checkHomogeneity _ [] _ = pure ()
        checkHomogeneity loc ((x, tx):xs) ((y, ty):ys) = do
          when (x == y) $
            addEq loc tx ty >> unify loc
          checkHomogeneity loc xs ((y, ty):ys)
          checkHomogeneity loc ((x, tx):xs) ys
fetchBindings (Pattern.At (Just t, _) x p) = (:) (x, t) <$> fetchBindings p
fetchBindings _ = pure []

tcPattern :: Pattern.LocPatternT -> StateT Typechecker Result Pattern.LocPatternT
tcPattern e@(Pattern.Literal (t, loc) l) = let tt = Literal.getType l
                                   in case t of
                                        Nothing -> tcPattern $ Pattern.Literal (Just tt, loc) l
                                        Just (Type.Variable i) -> do
                                          addEq loc (Type.Variable i) tt
                                          unify loc
                                          pure e
                                        Just t | t == tt -> pure e
                                               | otherwise -> throwError (loc, HeteroPrim t tt)
tcPattern (Pattern.Tuple (t, loc) el) = do
  ela <- mapM tcPattern el
  let targs = Prelude.map extractTypeP ela
  case t of
    Nothing -> tcPattern $ Pattern.Tuple (Just $ Type.Tuple targs, loc) ela
    Just (Type.Variable i) -> do
      addEq loc (Type.Variable i) (Type.Tuple targs)
      unify loc
      pure $ Pattern.Tuple (t, loc) ela
    Just (Type.Tuple targs1) -> do
      if Prelude.length targs /= Prelude.length targs1
        then throwError (loc, TupleArity (Prelude.length targs1) (Prelude.length targs))
        else checkLists loc targs targs1
      pure $ Pattern.Tuple (t, loc) ela
    Just t -> throwError (loc, HeteroPrim t $ Type.Tuple targs)
tcPattern (Pattern.Binding (Nothing, loc) x) = newVar >>= \i -> pure $ Pattern.Binding (Just $ Type.Variable i, loc) x
tcPattern e@(Pattern.Binding (Just _, _) _) = pure e
tcPattern (Pattern.Const (t, loc) i args) = do
  argst <- mapM tcPattern args
  Typechecker { scs, adts } <- get
  let k = scs !! i
  let ktargs = targs k
  let adt = adts !! parent k
  targsm <- unifyADTArgs loc ktargs (Prelude.map extractTypeP argst) Data.HashMap.empty
  targs <- mapM (\t -> case Data.HashMap.lookup t targsm of
                         Nothing -> Type.Variable <$> newVar
                         Just t -> pure t) $ vars adt
  let tk = Type.Data (parent k) targs
  case t of
    Nothing -> tcPattern $ Pattern.Const (Just tk, loc) i argst
    Just (Type.Data ti targs1) -> if parent k /= ti
                                  then throwError (loc, WrongADT ti (parent k))
                                  else do
      checkLists loc targs targs1 -- unifies
      pure $ Pattern.Const (t, loc) i argst
    Just (Type.Variable j) -> do
      addEq loc (Type.Variable j) tk
      unify loc
      pure $ Pattern.Const (t, loc) i argst
    Just t -> throwError (loc, HeteroPrim t tk)
tcPattern (Pattern.Or (t, loc) lp rp) = do
  lpt <- tcPattern lp
  rpt <- tcPattern rp
  addEq loc (extractTypeP lpt) (extractTypeP rpt)
  unify loc
  case t of
    Nothing -> tcPattern $ Pattern.Or (Just $ extractTypeP lpt, loc) lpt rpt
    Just t -> do
      addEq loc t (extractTypeP lpt)
      unify loc
      pure $ Pattern.Or (Just t, loc) lpt rpt
tcPattern (Pattern.At (t, loc) x p) = do
  pt <- tcPattern p
  case t of
    Nothing -> tcPattern $ Pattern.At (Just $ extractTypeP pt, loc) x pt
    Just t -> do
      addEq loc t (extractTypeP pt)
      unify loc
      pure $ Pattern.At (Just t, loc) x pt

tcBind :: (Text, Type.LocAnnT) -> StateT Typechecker Result (Text, (Type.Type, Location))
tcBind (x, (Nothing, loc)) = do
  i <- newVar
  pure (x, (Type.Variable i, loc))
tcBind (x, (Just t, loc)) = pure (x, (t, loc))
