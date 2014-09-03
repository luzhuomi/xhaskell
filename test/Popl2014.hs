
{-# LANGUAGE ScopedTypeVariables, QuasiQuotes, TemplateHaskell, MultiParamTypeClasses, FlexibleInstances #-} 
module Popl2014 where

import Language.XHaskell
import Prelude hiding (even)
[xh|

class Even a b where
  even :: a -> b
  
 
instance Even Int Bool where  
  even (x::Int) = (==) (mod x 2) 0  -- TODO: writing in infix notation still gives us inference problem.
  

instance Even a a where
  even (x::a) = x


mapStar :: (a -> b) -> Star a -> Star b
mapStar (f :: a -> b) = 
  \x -> case x of 
    { (x :: ()) -> x 
    ; (x :: a, xs :: Star a) -> (f x, mapStar f xs) 
    }
        
        
foo :: (Even a b) => Star a -> Star b        
foo (xs :: Star a) = mapStar (even:: a -> b) xs

|]


{-
It does not work, w/o functional dependencies, the behavior of foo really depends on the type annotations

*Popl2014> foo [1::Int,2,3] :: [Int]
[1,2,3]

*Popl2014> foo [1::Int,2,3] :: [Bool]
[False,True,False]

*Popl2014> foo [1::Int,2,3]

<interactive>:45:1:
    No instance for (Even Int b0) arising from a use of `foo'
    The type variable `b0' is ambiguous
    Possible fix: add a type signature that fixes these type variable(s)
    Note: there are several potential instances:
      instance Even a a -- Defined at Popl2014.hs:7:5
      instance Even Int Bool -- Defined at Popl2014.hs:7:5
    Possible fix: add an instance declaration for (Even Int b0)
    In the expression: foo [1 :: Int, 2, 3]
    In an equation for `it': it = foo [1 :: Int, 2, 3]

Adding funDeps breaks the the instance Even Int Bool and Even a a, because in popl14 paper, the second instance should be Even (a/Int) (a/Int)
-}