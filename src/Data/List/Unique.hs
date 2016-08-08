module Data.List.Unique where

data List a
   = Nil
   | Cons { hd :: a, tl :: List a }

{-@ data List a <p :: a -> a -> Prop>
         = Nil
         | Cons (x :: a) (xs :: List (a<p x>)) @-}

{-@ test :: List <{\x y -> x < y}> Int @-}
test :: List Int
test = Cons 4 (Cons 5 Nil)
