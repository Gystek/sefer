module Sefer.Pattern ( Pattern(..), LocPatternT ) where

import Data.Text
import qualified Sefer.Literal as Literal
import Sefer.Location
import qualified Sefer.Type as Type

data Pattern a = Literal { ann :: a, l :: Literal.Literal }
               | Tuple { ann :: a, args :: [Pattern a] }
               | Binding { ann :: a, x :: Text }
               | Const { ann :: a, i :: Int, cargs :: [Pattern a] }
               | Or { ann :: a, lp :: Pattern a, rp :: Pattern a }
               | At { ann :: a, x :: Text, p :: Pattern a }

type LocPatternT = Pattern Type.LocAnnT
