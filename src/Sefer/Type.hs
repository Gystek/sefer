module Sefer.Type ( Type(..), LocAnnT ) where

import Data.List
import Data.Text
import Sefer.Location

data Type = Character
           | Integer
           | Floating
           | Boolean
           | Tuple [Type]
           | Fun Type Type
           | Forall Int Type
           | TVar Int
           | EVar Int
          deriving (Eq)

instance Show Type where
  show Character = "Char"
  show Integer = "Int"
  show Floating = "Float"
  show Boolean = "Bool"
  show (Tuple xs) = "(" ++ Data.List.intercalate ", " (Prelude.map show xs) ++ ")"
  show (Fun a b) = show a ++ " -> " ++ show b
  show (Forall x t) = "∀t" ++ show x ++ "." ++ show t
  show (TVar t) = "t" ++ show t
  show (EVar t) = "?t" ++ show t

type LocAnnT = (Maybe Type, Location)
