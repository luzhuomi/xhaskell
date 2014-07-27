{-# LANGUAGE ScopedTypeVariables, QuasiQuotes, TemplateHaskell, MultiParamTypeClasses, FlexibleInstances #-} 
module NestedPatMatch where


import Data.Maybe
import Language.XHaskell

[xh|
data Foo = Foo (Star Bar) deriving Show
data Bar = Bar deriving Show


f :: Foo -> Choice Foo ()
f (Foo (x :: Bar)) = Foo x
f (Foo (x :: (Star Bar))) = ()


mapStar :: (a -> b) -> Star a -> Star b
mapStar (f :: a -> b) = 
  \x -> case x of 
    { (x :: ()) -> x 
    ; (x :: a, xs :: Star a) -> (f x, mapStar f xs) 
    }


g :: Star Foo -> Star Foo
g (xs :: (Star Foo)) = (mapStar f xs)

mapStar' :: (Foo -> Choice Foo ()) -> Star Foo -> Star (Choice Foo ())
mapStar' (f :: Foo -> Choice Foo ()) = 
  \x -> case x of
    { (x :: ()) -> x
    ; (x :: Foo, xs :: Star Foo) -> (f x, mapStar' f xs)
    }

|]


        


{-
*NestedPatMatch> f (Foo [Bar])
Left (Foo [Bar])
*NestedPatMatch> f (Foo [])
Right ()
-}