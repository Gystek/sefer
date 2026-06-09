module Sefer.Expr (Expr (..), LocExprT) where

import Data.Text
import Sefer.Location
import qualified Sefer.Type as Type

data Literal = Int deriving (Eq, Show)

data Expr a = Lit { ann :: a, lit :: Literal }
            | Tuple { ann :: a, els :: [Expr a] }
            | Var { ann :: a, v :: Text }
            | App { ann :: a, f :: Expr a, args :: [Expr a] }
            | Abs { ann :: a, fargs :: [(Text, a)], e :: Expr a }
            | Let { ann :: a, x :: (Text, a), y :: Expr a, z :: Expr a }
            | Cond { ann :: a, ei :: Expr a, et :: Expr a, ee :: Expr a }
            deriving (Eq, Show)

type LocExprT = Expr Type.LocAnnT
