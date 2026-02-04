module Expr ( Expr(..), LocExprTP0, LocExprTF0 ) where

import Control.Comonad.Cofree
import Data.Text
import Literal ( Literal )
import Location
import Pattern ( LocPattern )
import Type ( Type0 )

data Expr a = Literal Literal
            | Tuple [a]
            | Binding Text
            | Var Text
            | Const Int [a]
            | App a [a]
            -- `a` and not `Text` because the arguments carry a type
            | Abs [a] a
            -- let 0 = 1 in 2 ; same comment as for `Abs`
            | Let a a a
            | Cond a a a

type LocExprTP0 = Cofree Expr (Maybe Type0, Location)
type LocExprTF0 = Cofree Expr (Type0, Location)
