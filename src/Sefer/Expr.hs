module Sefer.Expr (Expr (..), Branch (..), LocExprT, LocBranchT) where

import Data.List
import Data.Text
import Sefer.Literal ( Literal )
import Sefer.Location
import qualified Sefer.Pattern as Pattern
import qualified Sefer.Type as Type

data Expr a = Literal { ann :: a, lit :: Literal }
            | Tuple { ann :: a, els :: [Expr a] }
            | Var { ann :: a, v :: Text }
            | Const { ann :: a, k :: Int, cargs :: [Expr a] }
            | App { ann :: a, f :: Expr a, args :: [Expr a] }
            | Abs { ann :: a, fargs :: [(Text, a)], e :: Expr a }
            -- let x = y in z
            | Let { ann :: a, x :: (Text, a), y :: Expr a, z :: Expr a }
            | Cond { ann :: a, ei :: Expr a, et :: Expr a, ee :: Expr a }
            | Match { ann :: a, e :: Expr a, branches :: [Branch a] }
            deriving (Eq)

instance Show a => Show (Expr a) where
  show (Literal ann lit) = show lit ++ "@" ++ show ann
  show (Tuple ann els) = "(" ++ Data.List.intercalate ", " (Prelude.map show els) ++ ")" ++ "@" ++ show ann
  show (Var ann v) = unpack v ++ "@" ++ show ann
  show (Const ann k args) = "Const$" ++ show k ++ " " ++ Data.List.unwords (Prelude.map show args) ++ "@" ++ show ann
  show (App ann f args) = show f ++ " " ++ Data.List.unwords (Prelude.map show args) ++ "@" ++ show ann
  show (Abs ann args ret) = "fun " ++ Data.List.unwords (Prelude.map show args) ++ " = " ++ show ret ++ "@" ++ show ann
  show (Let ann x y z) = "let " ++ show x ++ " = " ++ show y ++ " in " ++ show z ++ "@" ++ show ann
  show (Cond ann ei et ee) = "if " ++ show ei ++ " then " ++ show et ++ " else " ++ show ee ++ "@" ++ show ann
  show (Match ann e br) = "match " ++ show e ++ "{\n" ++ Data.List.intercalate ",\n" (Prelude.map show br) ++ "\n}" ++ "@" ++ show ann

data Branch a = Branch a (Pattern.Pattern a) (Maybe (Expr a)) (Expr a)
              deriving (Eq)

instance Show a => Show (Branch a) where
  show (Branch ann p g e) = show p ++ (case g of
                                        Nothing -> ""
                                        Just g -> " if " ++ show g
                                      )
                            ++ " -> " ++ show e ++ "@" ++ show ann

type LocBranchT = Branch Type.LocAnnT

type LocExprT = Expr Type.LocAnnT
