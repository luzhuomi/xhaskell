
{-# LANGUAGE ScopedTypeVariables, QuasiQuotes, TemplateHaskell, MultiParamTypeClasses, FlexibleInstances #-} 
module Simple where

import Language.XHaskell

[xh|

g :: Choice Int Bool -> Choice Int Bool
g (x :: Int) = x

f :: Star Int -> Star (Choice Int Bool)
f (x::Star Int, y::Int) = g y

h :: Star (Choice Int a) -> Star (Choice Int a)
h (x :: a) = x

|]