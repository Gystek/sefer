module Sefer.Pattern ( Pattern(..), LocPatternT ) where

import Data.List
import Data.Text
import qualified Sefer.Literal as Literal
import Sefer.Location
import qualified Sefer.Type as Type

data Pattern a = Literal { ann :: a, l :: Literal.Literal }
               | Tuple { ann :: a, args :: [Pattern a] }
               | Binding { ann :: a, x :: Text }
               | Const { ann :: a, i :: Int, cargs :: [Pattern a] }
               | Or { ann :: a, lp :: Pattern a, rp :: Pattern a }
               | At { ann :: a, x :: Text, p :: Pattern a }
               deriving (Eq)

instance Show a => Show (Pattern a) where
  show (Literal ann lit) = show lit ++ "@" ++ show ann
  show (Tuple ann els) = "(" ++ Data.List.intercalate ", " (Prelude.map show els) ++ ")" ++ "@" ++ show ann
  show (Binding ann v) = unpack v ++ "@" ++ show ann
  show (Const ann k args) = "Const$" ++ show k ++ " " ++ Data.List.intercalate " " (Prelude.map show args) ++ "@" ++ show ann
  show (Or ann lp rp) = show lp ++ " | " ++ show rp ++ "@" ++ show ann
  show (At ann x p) = unpack x ++ " <- " ++ show p ++ "@" ++ show ann


type LocPatternT = Pattern Type.LocAnnT
