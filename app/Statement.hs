module Statement ( ADType(..), Constructor(..) ) where

import Type ( Type0 )

data ADType = ADType { nVar :: Int }

data Constructor = Constructor { parent :: Int, targs :: [Type0] }
