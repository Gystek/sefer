module Type ( Type0(..) ) where

data Type0 = Character
           | Integer
           | Floating
           | Boolean
           | Tuple [Type0]
           -- TODO: add rigid tvars
           | Variable Int
           | Fun [Type0] Type0
           -- data T a b = ...
           -- T Int Int :: Data 0 [Int Int]
           | Data Int [Type0]
             deriving (Show)
