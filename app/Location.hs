module Location ( Location(..) ) where

import Data.Text

data Location = Location { f :: Text, s :: (Int, Int), e :: (Int, Int) }

instance Show Location where
  show Location { f = f, s = (sl, sc), e = (el, ec) }
    = show f
      ++ ":"
      ++ show sl
      ++ "."
      ++ show sc
      ++ "-"
      ++ if sl == el
         then show ec
         else show el ++ "." ++ show ec
