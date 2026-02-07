module Statement ( ADType(..), Constructor(..) ) where

import Type

data ADType = ADType { nVar :: Int }

data Constructor = Constructor { parent :: Int, targs :: [Type] }
