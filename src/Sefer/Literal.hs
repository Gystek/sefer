module Sefer.Literal ( Literal(..), getType ) where

import qualified Sefer.Type as Type

data Literal = Character Char
             | Integer Int
             | Floating Float
             | Boolean Bool
               deriving (Eq)

instance Show Literal where
  show (Character c) = '\'':c:"'"
  show (Integer i) = show i
  show (Floating f) = show f
  show (Boolean b) = show b

getType :: Literal -> Type.Type
getType (Character _) = Type.Character
getType (Integer _) = Type.Integer
getType (Floating _) = Type.Floating
getType (Boolean _) = Type.Boolean
