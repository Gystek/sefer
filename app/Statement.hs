module Statement ( ADType(..), SumConstructor(..) ) where

import Type ( Type0 )

data ADType = ADType { nVar :: Int }

data SumConstructor = SumConstructor { parent :: Int, targs :: [Type0] }
