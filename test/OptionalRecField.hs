{-# LANGUAGE ScopedTypeVariables, QuasiQuotes, TemplateHaskell, MultiParamTypeClasses, FlexibleInstances #-} 
module OptionalRecField where


import Data.Maybe
import Language.XHaskell

[xh|
data Tweet = Tweet { user :: User
                   , contributors :: (Star User)
                   , place :: (Choice Place ()) }
             deriving Show
                      
data User = User { favorite_count :: Int       
                 , friends_count :: Int
                 , time_zone :: String
                 , user_id :: Int
                 , name :: String
                 , statuses_count :: Int
                 , screen_name :: String 
                 }
            deriving (Show)
                      
                     
data Place = Place { pname :: String }                      
             deriving Show

mapStar :: (a -> b) -> Star a -> Star b
mapStar (f :: a -> b) = 
  \x -> case x of 
    { (x :: ()) -> x 
    ; (x :: a, xs :: Star a) -> (f x, mapStar f xs) 
    }
  

-- find all tweets that has a location

tweetsWithLocation :: Star Tweet -> Star Tweet
tweetsWithLocation (ts :: Star Tweet) = 
  mapStar 
  ( \(t :: Tweet) -> case t of 
       { Tweet{place = p :: Place} -> t
       ; Tweet{} -> () } :: Choice Tweet () ) ts
                     
  

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
                 -- ommitable, contributors = ()
                 , place = Place "Singapore" 
                 } , 
           Tweet { user = luzm }
         )
|]


{-

*OptionalRecField> tweets
[Tweet {user = User {favorite_count = 1, friends_count = 1, time_zone = "GMT+8", user_id = 10294596, name = "Kenny Lu", statuses_count = 289, screen_name = "luzm"}, contributors = [], place = Left (Place {pname = "Singapore"})},Tweet {user = User {favorite_count = 1, friends_count = 1, time_zone = "GMT+8", user_id = 10294596, name = "Kenny Lu", statuses_count = 289, screen_name = "luzm"}, contributors = [], place = Right ()}]
*OptionalRecField> tweetsWithLocation tweets
[Tweet {user = User {favorite_count = 1, friends_count = 1, time_zone = "GMT+8", user_id = 10294596, name = "Kenny Lu", statuses_count = 289, screen_name = "luzm"}, contributors = [], place = Left (Place {pname = "Singapore"})}]

-}