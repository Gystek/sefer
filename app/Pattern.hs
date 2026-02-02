module Pattern ( LocPattern, Pattern(..) ) where

import Control.Comonad.Cofree
import Data.Text
import Literal ( Literal )
import Location ( Location )

data Pattern a = Const Int [a]
               | Tuple [a]
               | Binding Text
               | Literal Literal

type LocPattern = Cofree Pattern Location
