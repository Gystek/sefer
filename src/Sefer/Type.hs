module Sefer.Type ( Type(..), LocAnnT ) where

import Data.List
import Data.Text
import Sefer.Location

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
          deriving (Eq)

instance Show Type where
  show Character = "Char"
  show Integer = "Int"
  show Floating = "Float"
  show Boolean = "Bool"
  show (Tuple xs) = "(" ++ Data.List.intercalate ", " (Prelude.map show xs) ++ ")"
  show (RVar x) = unpack x
  show (Variable i) = "?t" ++ show i
  show (Fun args ret) = Data.List.intercalate " -> " (Prelude.map show args) ++ " -> " ++ show ret
  show (Data i vars) = "Data$" ++ show i ++ "[" ++ Data.List.intercalate ", " (Prelude.map show vars) ++ "]"

type LocAnnT = (Maybe Type, Location)
