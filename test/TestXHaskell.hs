{-# LANGUAGE ScopedTypeVariables, QuasiQuotes, TemplateHaskell, MultiParamTypeClasses, FlexibleInstances #-} 
module TestXHaskell where

import Language.XHaskell

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

 


e.g. 


tweet = {"in_reply_to_status_id_str":null
        ,"contributors":null
        ,"place":null
        ,"in_reply_to_screen_name":null
        ,"text":"Test"
        ,"favorited":false
        ,"in_reply_to_user_id_str":null
        ,"coordinates":null
        ,"geo":null
        ,"retweet_count":0
        ,"created_at":"Fri Jul 13 09:38:00 +0000 2012"
        ,"source":"web"
        ,"in_reply_to_user_id":null
        ,"in_reply_to_status_id":null
        ,"retweeted":false
        ,"id_str":"223712876576260096"
        ,"truncated":false
        ,"user":{"favourites_count":10
                ,"friends_count":42
                ,"profile_background_color":"C6E2EE"
                ,"following":null
                ,"profile_background_tile":false
                ,"profile_background_image_url_https":"https:\/\/si0.twimg.com\/images\/themes\/theme2\/bg.gif"
                ,"followers_count":38
                ,"profile_image_url":"http:\/\/a0.twimg.com\/profile_images\/60558692\/KennyMugShot_normal.jpg"
                ,"contributors_enabled":false
                ,"geo_enabled":false
                ,"created_at":"Tue Sep 23 03:08:29 +0000 2008"
                ,"profile_sidebar_fill_color":"DAECF4"
                ,"description":"Circos.com, Computer Science, Phd, National University of Singapore"
                ,"listed_count":1
                ,"follow_request_sent":null
                ,"time_zone":"Singapore"
                ,"url":"http:\/\/sites.google.com\/site\/luzhuomi\/"
                ,"verified":false
                ,"profile_sidebar_border_color":"C6E2EE"
                ,"default_profile":false
                ,"show_all_inline_media":false
                ,"is_translator":false
                ,"notifications":null
                ,"profile_use_background_image":true
                ,"protected":false
                ,"profile_image_url_https":"https:\/\/si0.twimg.com\/profile_images\/60558692\/KennyMugShot_normal.jpg"
                ,"location":"Singapore"
                ,"id_str":"16414559"
                ,"profile_text_color":"663B12"
                ,"name":"Kenny"
                ,"statuses_count":199
                ,"profile_background_image_url":"http:\/\/a0.twimg.com\/images\/themes\/theme2\/bg.gif"
                ,"id":16414559
                ,"default_profile_image":false
                ,"lang":"en"
                ,"utc_offset":28800
                ,"profile_link_color":"1F98C7"
                ,"screen_name":"luzm"}
        ,"id":223712876576260096
        ,"entities":{"user_mentions":[],"urls":[],"hashtags":[]}
        }


-}




[xh|
data Tweet = Tweet { contributors :: (Star User)
                   , place :: (Or Place ())
                   , text :: String
                   , favorited :: (Or Bool ())
                   , user :: User
                   , created_at :: String
                   , id :: Int
                   , entities :: Entities
                   }
             
data Entities = Entities { user_mentions :: Star User             
                         , urls :: Star String
                         , hashtags :: Star String
                         }
                
data User = User { favorite_count :: Int       
                 , friends_count :: Int
                 , time_zone :: String
                 , id :: Int
                 , name :: String
                 , statuses_count :: Int
                 , screen_name : String 
                 }
 



|] 

