module Sefer.Statement ( ADType(..), Constructor(..) ) where

import Data.Text
import qualified Sefer.Type as Type

data ADType = ADType { vars :: [Text] } deriving Show

data Constructor = Constructor { parent :: Int, targs :: [Type.Type] } deriving Show
