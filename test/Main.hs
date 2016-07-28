
module Main (main) where

import Test.Tasty
import qualified Test.Tasty.QuickCheck as QC
import Test.QuickCheck

import Prelude hiding (id)
import Control.Category (id)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.BinaryList (BinList)
import qualified Data.BinaryList as BL
import Data.BinaryList.Serialize (toDecoded, fromDecoded)
import Data.BinaryList.Algorithm.BinaryTransform

instance Arbitrary a => Arbitrary (BinList a) where
  arbitrary = do
    e <- choose (0,16)
    BL.replicateA e arbitrary

instance Arbitrary a => Arbitrary (Vector a) where
  arbitrary = do
    e <- choose (0,16) :: Gen Int
    V.replicateM (2^e) arbitrary

bijectionTest :: (Eq a, Eq b) => Bijection a b -> a -> b -> Bool
bijectionTest (Bijection f f') x x' =
  (f' (f x) == x) && (f (f' x') == x')

type BLTransform a = Bijection (BinList a) (BinList a)
type VTransform a = Bijection (Vector a) (Vector a)

main :: IO ()
main = defaultMain $ testGroup "Transform Tests"
  [ QC.testProperty "leftBinaryTransform id" $ bijectionTest (leftBinaryTransform id :: BLTransform Int)
  , QC.testProperty "leftBinaryTransformVector id" $ bijectionTest (leftBinaryTransformVector id :: VTransform Int)
  , QC.testProperty "leftRetransformDecoded id" $ \xs -> fromDecoded (leftRetransformDecoded id (toDecoded xs)) == Right (xs :: BinList Int)
  , QC.testProperty "rightBinaryTransform id" $ bijectionTest (rightBinaryTransform id :: BLTransform Int)
    ]
