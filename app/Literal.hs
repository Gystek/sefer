module Literal ( Literal(..), getType ) where

import Type

data Literal = Character Char
             | Integer Int
             | Floating Float
             | Boolean Bool
               deriving (Show)

getType :: Literal -> Type
getType (Literal.Character _) = Type.Character
getType (Literal.Integer _) = Type.Integer
getType (Literal.Floating _) = Type.Floating
getType (Literal.Boolean _) = Type.Boolean
