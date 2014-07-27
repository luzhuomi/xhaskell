{-# LANGUAGE ScopedTypeVariables, QuasiQuotes, TemplateHaskell, MultiParamTypeClasses, FlexibleInstances #-} 
module XPathFullAnnotation where

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
    \t -> (mapStar :: ((a -> Star t) -> Star a -> Star (Star t))) 
          ((\x -> ((//) :: (a -> t -> (Star t))) x t) :: (a -> (Star t)))
          xs 
          
instance XPath P P where           
  (//) (x::P) = \p -> x


instance XPath Body P where  
  (//) (Body (ps::(Star P))) = \p -> ((//) :: (Star P) -> P -> Star P) ps p
  
instance XPath Head P where
  (//) Head = \p -> ()
  
instance XPath Html P where  
  (//) (Html (h::Head) (b::Body)) = \p -> ( ((//) :: Head -> P -> Star P) h p,
                                            ((//) :: Body -> P -> Star P) b p )


mapStar :: (a -> b) -> Star a -> Star b
mapStar (f :: a -> b) = 
  \x -> case x of 
    { (x :: ()) -> x 
    ; (x :: a, xs :: Star a) -> (f x, (mapStar :: ((a -> b) -> Star a -> Star b)) f xs) 
    }


|] 

