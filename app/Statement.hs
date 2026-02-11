module Statement ( ADType(..), Constructor(..) ) where

import Data.Text
import Type

data ADType = ADType { vars :: [Text] }

data Constructor = Constructor { parent :: Int, targs :: [Type] }
