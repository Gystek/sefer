module Pattern ( Pattern(..), LocPattern ) where

import Data.Text
import Literal
import Location
import Type

data Pattern a = Literal a Literal
               | Tuple a [Pattern a]
               | Binding a Text
               | Const a Int [Pattern a]
               | Or a (Pattern a) (Pattern a)
               | At a Text (Pattern a)

type LocPattern = Pattern (Maybe Type, Location)
