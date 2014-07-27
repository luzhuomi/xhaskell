{-# LANGUAGE ScopedTypeVariables, QuasiQuotes, TemplateHaskell, MultiParamTypeClasses, FlexibleInstances #-} 
module XPathNoAnnotation where

import Language.XHaskell


[xh|

data Html = Html Head Body
 
data Head = Head

data Body = Body (Star P)

data P = P deriving Show
 

class XPath a b where 
  (//) :: a -> b -> Star b


instance XPath a () where  
  (//) (x::a) = \y -> () 


instance XPath a t => XPath (Star a) t where  
  (//) (xs::Star a) = 
    \t -> mapStar (\(x::a) -> (//) x t) xs 
    
instance XPath P P where           
  (//) (x::P) = \p -> x

instance XPath Body P where  
  (//) (Body (ps::(Star P))) = \p -> (//) ps p

instance XPath Head P where
  (//) Head = \p -> ()
  

instance XPath Html P where  
  (//) (Html (h::Head) (b::Body)) = \p -> ((//) h p, (//) b p)


mapStar :: (a -> b) -> Star a -> Star b
mapStar (f :: a -> b) = 
  \x -> case x of 
    { (x :: ()) -> x 
    ; (x :: a, xs :: Star a) -> (f x, mapStar f xs) 
    }


|] 

