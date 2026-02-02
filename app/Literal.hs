module Literal ( Literal(..), getType0 ) where

import Type

data Literal = Character Char
             | Integer Int
             | Floating Float
             | Boolean Bool
               deriving (Show)

getType0 :: Literal -> Type0
getType0 (Literal.Character _) = Type.Character
getType0 (Literal.Integer _) = Type.Integer
getType0 (Literal.Floating _) = Type.Floating
getType0 (Literal.Boolean _) = Type.Boolean
