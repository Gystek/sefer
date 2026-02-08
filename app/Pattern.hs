module Pattern ( Pattern(..), LocPatternT ) where

import Data.Text
import Literal
import Location
import Type

data Pattern a = Literal { ann :: a, l :: Literal }
               | Tuple { ann :: a, args :: [Pattern a] }
               | Binding { ann :: a, x :: Text }
               | Const { ann :: a, i :: Int, cargs :: [Pattern a] }
               | Or { ann :: a, lp :: Pattern a, rp :: Pattern a }
               | At { ann :: a, x :: Text, p :: Pattern a }

type LocPatternT = Pattern LocAnnT
