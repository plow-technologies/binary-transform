
module Main (main) where

import Prelude hiding (id, (.))
import Control.Category
import qualified Data.BinaryList as BL
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.BinaryList.Serialize (toDecoded)
import Data.BinaryList.Algorithm.BinaryTransform

import Criterion.Main

blist :: BL.BinList Int
blist = BL.generate 14 id

blistL, blistR :: BL.BinList Int
blistL = direct ( leftBinaryTransform id) blist
blistR = direct (rightBinaryTransform id) blist

vec :: Vector Int
vec = V.generate (2^14) id

vecL :: Vector Int
vecL = direct (leftBinaryTransformVector id) vec

main :: IO ()
main = defaultMain
  [ bench  "left-transform"         $ nf (direct  $  leftBinaryTransform       id) blist
  , bench  "left-transform-vec"     $ nf (direct  $  leftBinaryTransformVector id) vec
  , bench  "left-transform-inv"     $ nf (inverse $  leftBinaryTransform       id) blistL
  , bench  "left-transform-inv-vec" $ nf (inverse $  leftBinaryTransformVector id) vecL
  , bench  "left-transform-inv-dec" $ nf ( leftInverseBinaryTransformDec       id) (toDecoded blistL)
  , bench "right-transform"         $ nf (direct  $ rightBinaryTransform       id) blist
  , bench "right-transform-inv"     $ nf (inverse $ rightBinaryTransform       id) blistR
  , bench "right-transform-inv-dec" $ nf (rightInverseBinaryTransformDec       id) (toDecoded blistR)
    ]
