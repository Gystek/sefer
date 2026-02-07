module Expr ( Expr(..), Branch(..), LocExprT ) where

import Data.Text
import Literal ( Literal )
import Location
import Pattern
import Type ( Type )

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

data Branch a = Branch { pat :: Pattern a
                       , guard :: Maybe (Expr a)
                       , body :: Expr a
                       }

type LocExprT = Expr (Maybe Type, Location)
