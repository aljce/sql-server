{-# LANGUAGE ViewPatterns #-}
import Test.QuickCheck
import Test.Framework
import Test.Framework.Providers.QuickCheck2

import qualified Data.Set as S
import Data.Vector hiding (foldr)
import Data.Vector.Unique

newtype Sorted a = Sorted (Vector a) deriving (Show)

unionsCorrectlyProp :: (Ord a) => OrderedList a -> OrderedList a -> Bool
unionsCorrectlyProp (Ordered (fromList -> v1)) (Ordered (fromList -> v2)) =
  toSet (unionV v1 v2) == toSet v1 `S.union` toSet v2
  where toSet = foldr S.insert S.empty

tests :: [Test]
tests = [ testGroup "Union" [ testProperty "UnionV" (unionsCorrectlyProp :: OrderedList Int -> OrderedList Int -> Bool) ] ]

main :: IO ()
main = defaultMain tests
