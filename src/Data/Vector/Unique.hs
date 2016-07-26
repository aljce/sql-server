{-# LANGUAGE ScopedTypeVariables #-}
module Data.Vector.Unique where

import qualified Data.Vector as V
import Data.Vector (Vector)
import qualified Data.Vector.Mutable as M
import Data.Vector.Mutable (MVector)
import Control.Monad.ST (ST)

{-@ measure mvlen :: MVector s a -> Int @-}
{-@ invariant {mv:MVector s a | 0 <= mvlen mv } @-}

{-@ assume mnew :: n:Nat -> ST s ({mv:MVector s a | mvlen mv == n}) @-}
mnew :: Int -> ST s (M.MVector s a)
mnew = M.new

{-@ assume mtake :: n:Nat -> in:{in:MVector s a | n <= mvlen in } -> {out:MVector s a | mvlen out = n } @-}
mtake :: Int -> MVector s a -> MVector s a
mtake = M.take

{-@ assume mdrop :: n:Nat ->
                    in:{in:MVector s a | n <= mvlen in } ->
                    {out:MVector s a | mvlen out = mvlen in - n } @-}
mdrop :: Int -> MVector s a -> MVector s a
mdrop = M.drop

{-@ assume mslice :: start:Nat -> length:Nat ->
                     {in:MVector s a  | start + length <= mvlen in } ->
                     {out:MVector s a | mvlen out = length } @-}
mslice :: Int -> Int -> MVector s a -> MVector s a
mslice = M.slice

{-@ assume mwrite :: in:MVector s a -> index:{n:Nat | n <= mvlen in } -> a -> ST s () @-}
mwrite :: MVector s a -> Int -> a -> ST s ()
mwrite = M.write

{-@ assume vcopy :: target:MVector s a ->
                    source:{source:Vector a | mvlen target = vlen source } ->
                    ST s () @-}
vcopy :: MVector s a -> Vector a -> ST s ()
vcopy = V.copy

{-@ assume V.drop :: n:Nat ->
                     in:{in:Vector a | n <= vlen in } ->
                     {out:Vector a | vlen out = vlen in - n } @-}

{-@ predicate Bounded T V S M = T + vlen V - S <= mvlen M @-}
{-@ unionV :: v1:Vector -> v2:Vector a -> Vector a @-}
unionV :: forall a. Ord a => V.Vector a -> V.Vector a -> V.Vector a
unionV v1 v2 = V.create (mnew (V.length v1 + V.length v2) >>= go 0 0 0)
    {-@ go :: sindex1:{n:Nat | n <= vlen v1 } ->
              sindex2:{n:Nat | n <= vlen v2 } ->
              tindex:{n:Nat | true } ->
              target:{mv:MVector s a | Bounded tindex v1 sindex1 mv &&
                                       Bounded tindex v2 sindex2 mv } ->
              ST s (MVector s a) / [mvlen target - tindex] @-}
  where go :: Int -> Int -> Int -> MVector s a -> ST s (MVector s a)
        go sindex1 sindex2 tindex target = case V.length v1 <= sindex1 of
          True -> do
            vcopy (mslice tindex (V.length v2 - sindex2) target) (V.drop sindex2 v2)
            pure (mtake (tindex + V.length v2 - sindex2) target)
          False -> case V.length v2 <= sindex2 of
            True -> do
              vcopy (mslice tindex (V.length v1 - sindex1) target) (V.drop sindex1 v1)
              pure (mtake (tindex + V.length v1 - sindex1) target)
            False -> let e1 = v1 V.! sindex1
                         e2 = v2 V.! sindex2
                     in case compare e1 e2 of
                          LT -> do
                            mwrite target tindex e1
                            -- pure target
                            go (sindex1 + 1) sindex2 (tindex + 1) target
                          EQ -> do
                            mwrite target tindex e1
                            go (sindex1 + 1) (sindex2 + 1) (tindex + 1) target
                          GT -> do
                            mwrite target tindex e2
                            -- pure target
                            go sindex1 (sindex2 + 1) (tindex + 1) target
