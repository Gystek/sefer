module Type ( Type(..) ) where

data Type = Character
           | Integer
           | Floating
           | Boolean
           | Tuple [Type]
           -- TODO: add rigid tvars
           | Variable Int
           | Fun [Type] Type
           -- data T a b = ...
           -- T Int Int :: Data 0 [Int Int]
           | Data Int [Type]
             deriving (Show, Eq)
