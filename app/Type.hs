module Type ( Type(..), LocAnnT ) where

import Data.Text
import Location

data Type = Character
           | Integer
           | Floating
           | Boolean
           | Tuple [Type]
           | RVar Text
           | Variable Int
           | Fun [Type] Type
           -- data T a b = ...
           -- T Int Int :: Data 0 [Int Int]
           | Data Int [Type]
             deriving (Show, Eq)

type LocAnnT = (Maybe Type, Location)
