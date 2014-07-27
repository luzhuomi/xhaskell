{-# LANGUAGE ScopedTypeVariables, QuasiQuotes, TemplateHaskell, MultiParamTypeClasses, FlexibleInstances #-} 
module Mongo1 where

import Language.XHaskell
import Data.Maybe 

{- mongoDB style query


 db.<tablename>.find( Q ) 

 <query> Q :: =  Q,Q    (And)
             |   $or : [Q]   (Or)
             |   simple_field : P
             |   array_field : P   -- return all the elements that satisfies P

 <predicate> P :: = V  (equality test)
                  | $eq : V (equality test)
                  | $lt : V (less than)
                  | $gt : V (greater than)
                  | $in : [V]   (membership test)
                  | [V]
 <value> V :: = 1 | 'A' | "hello" | True | False

-}

-- only handling the simple query w/o conjuction and disjuction


[xh|
data Tweet = Tweet { user :: User
                   , contributors :: (Star User)
                   , place :: (Choice Place ()) }
             deriving (Show)
             
                
data User = User { favorite_count :: Int       
                 , friends_count :: Int
                 , time_zone :: String
                 , user_id :: Int
                 , name :: String
                 , statuses_count :: Int
                 , screen_name :: String 
                 }
            deriving (Show, Ord, Eq)
data Place = Place String deriving (Show, Ord, Eq)

 
-- find all tweets that has a location

mapStar :: (a -> b) -> Star a -> Star b
mapStar (f :: a -> b) = 
  \x -> case x of 
    { (x :: ()) -> x 
    ; (x :: a, xs :: Star a) -> (f x, mapStar f xs) 
    }
  

tweetsWithLocation :: Star Tweet -> Star Tweet
tweetsWithLocation (ts :: Star Tweet) = 
  mapStar 
  ( \(t :: Tweet) -> case t of 
       { Tweet{place= p :: Place} -> t
       ; Tweet{} -> () } :: Choice Tweet () ) ts



find  :: Ord b => Star a -> (a -> Star b) -> (b -> b -> Bool) -> b -> Star a
find (ts :: Star a) = 
  \(acc :: a -> Star b) -> 
  \(cmp :: b -> b -> Bool) ->
  \(p :: b) ->   
  mapStar (\(t::a) -> 
            case acc t of
              { (p' :: b, ps :: Star b) -> 
                   if cmp p p'
                   then t 
                   else ()
              ; (e :: ()) -> () 
              } :: (Choice a ())) ts
  
  
{-   
 ts.find( { place : "Singapore" } )
-}

sgTweets :: Star Tweet
sgTweets = find tweets place (==) (Place "Singapore") 

-- this does not work now as the local type inference does not allow args type to be polymorphic. Maybe we should decide which subset of arg is good enough to ground all the polymoprhic types. 
-- find :: Eq b => Star a -> (a -> Star b) -> (b -> b -> Bool) -> b -> Star a
-- tweets :: Star Tweet                ===> Star Tweet <: Star a  ===> Tweet <: a <: Top   #1

-- place :: Tweet -> Choice Place ()   ===>  Tweet -> Choice Place () <: a -> Star b   ===>   Bot <: a <: Tweet  \wedge  Choice Place () <: Star b  #2
-- Place "Singapore" :: Place          ===> Place <: b  ===> Place <: b <: Top             #3
-- == :: forall c. Eq c => c -> c -> Bool   ===> forall c. Eq c => c -> (c -> Bool) <: b -> (b -> Bool)
---        ===>  {c} |-  c <: b  \wedge {c} |- c <: b \wdedge  Bool <: Bool  ===>  c \down_{c} Bot hence ===> Bot <: b <: Top  #4 

luzmTweets :: Star Tweet
-- luzmTweets = find tweets user (==) luzm
luzmTweets = find tweets ((.) screen_name user) (==) "luzm"


    
{-     
 tweets.find( { place : "Singapore", contributor : "luzm" }
 -- does not support AND-query yet.
-} 
    
luzm :: User  
luzm = User { favorite_count = 1,
              friends_count = 1,
              time_zone = "GMT+8",
              user_id = 10294596,
              name = "Kenny Lu",
              statuses_count = 289,
              screen_name = "luzm"
            }
  
tweets :: Star Tweet
tweets = ( Tweet { user = luzm 
                          -- , contributors = ()
                 , place = Place "Singapore" 
                 } , 
           Tweet { user = luzm }
         )
                 

|] 


       
