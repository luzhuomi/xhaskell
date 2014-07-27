{-# LANGUAGE TemplateHaskell #-}

module Language.XHaskell.TypeSpec where

import Language.Haskell.TH
import Language.Haskell.TH.Quote -- gives us QuasiQuoter
import Language.Haskell.TH.Syntax
import Data.Map
import Data.List (nub,sort)
import Data.Char


-- counting stuff
import System.IO.Unsafe
-- import Data.IORef


type Sym = [Char] -- the string representation of the type name

data Sig = Sig -- wildcard symbol '.'

data Re = L Sym 
        | Star Re
        | Pair Re Re
        | Choice Re Re
        | Eps
        | Phi
          deriving (Show, Eq, Ord)
          
sig :: Re -> [Sym]
-- sig (L Sig)        = []
sig (L s)          = [s]
sig (Star r)       = sig r
sig (Pair r1 r2)   = nub (sort (sig r1 ++ sig r2))
sig (Choice r1 r2) = nub (sort (sig r1 ++ sig r2))
sig Eps            = []
sig Phi            = []
                   
          
posEps :: Re -> Bool
posEps (Star _) = True
posEps Eps = True
posEps (Pair r1 r2) = posEps r1 && posEps r2
posEps (Choice r1 r2) = posEps r1 || posEps r2
posEps _ = False
          
           
isPhi :: Re -> Bool           
isPhi Phi = True
isPhi (Pair r1 r2) = isPhi r1 || isPhi r2
isPhi (Choice r1 r2) = isPhi r1 && isPhi r2
isPhi _ = False
           
-- PD
pD :: Re -> Sym -> [Re]           
pD (Star r) l = nub [ Pair r' (Star r) | r' <- pD r l ]
pD (Pair r1 r2) l | posEps r1 = nub ([ Pair r' r2 | r' <- pD r1 l ] ++ pD r2 l)
                   | otherwise = nub [ Pair r' r2 | r' <- pD r1 l ]
pD (Choice r1 r2) l = nub (pD r1 l ++ pD r2 l)
pD (L l') l 
  -- | l' == Sig = [ Eps ]
  | l == l' = [ Eps ]
  | otherwise =  []
pD Eps l = []                           
pD Phi l = []


-- pd 
pd :: Re -> Sym -> Re
pd r l = unList (pD r l)
  where unList [] = Phi
        unList [r] = r
        unList (r:rs) = Choice r (unList rs)
           
{- |r|
|L Char| = Char
|Pair r1 r2| = (|r1|,|r2|)
|Choice r1 r2| = Either |r1| |r2|
|Star r| = [|r|]
|Eps| = ()
|Phi| = ??
-}

{-
isTyVarName :: Sym -> Bool
isTyVarName (c:_) = isLower c 
isTyVarName _ = False



tyTrans :: Re -> Q Type
tyTrans (L sym) = do 
  { name <- newName sym
  ; if (isTyVarName sym)
    then return (VarT name)
    else return (ConT name)
  }
tyTrans (Pair r1 r2) = [t| ($(tyTrans r1), $(tyTrans r2)) |]
tyTrans (Choice r1 r2) = [t| Either $(tyTrans r1) $(tyTrans r2)|]
tyTrans (Star r) = [t| [$(tyTrans r)]|]
tyTrans Eps = [t|()|]
tyTrans Phi = error "tyTrans is applied to Phi"
-}

-- mkEmpty :: r -> [| v |]          
-- \eps \in r                  
--  |- v : r
mkEmpty :: Re -> Q Exp 
mkEmpty (Star _) = [| [] |]
mkEmpty (Pair r1 r2) = [| ( $(mkEmpty r1),  $(mkEmpty r2)) |]
mkEmpty (Choice r1 r2) | posEps r1 = [| Left $(mkEmpty r1) |]
                       | posEps r2 = [| Right $(mkEmpty r2) |]
                       | otherwise = [| error "mkEmpty is apply to non-empty choice, this should not be triggered" |] -- to handle A <= (A|B)
mkEmpty Eps = [| () |]                                     
mkEmpty Phi = [| undefined |] -- why do we need this?
mkEmpty (L _) = [| undefined |] 

-- injE :: r' -> r -> l -> [| vl -> vr' -> vr  |]
--    r' \in (pD r l)  \wedge
--    |- vl : l  \wedge
--    |- vr' : r' \wedge
--    |- vr : r 
injE :: Re -> Re -> Sym -> Q Exp
injE (Pair r' r'') (Star r) l = 
  [| \ vl (v1,vs) -> (:) ($(injE r' r l) vl v1)  vs  |]
injE r' (Pair r1 r2) l 
  | r' `elem` (pD r2 l) && posEps r1 =
    [| \ vl v -> ($(mkEmpty r1), ($(injE r' r2 l) vl v)) |]
  | otherwise = 
      case r' of
        (Pair r1' r2') ->  [| \ vl (v1,v2) -> (($(injE r1' r1 l) vl v1),v2) |]
        
injE r' (Choice r1 r2) l 
  | r' `elem` (pD r1 l) = [| \ vl v -> Left ($(injE r' r1 l) vl v) |]
  | r' `elem` (pD r2 l) = [| \ vl v -> Right ($(injE r' r2 l) vl v) |]
                          
injE Eps (L c) c' | c == c' = [| \ vl () -> vl |]



-- injS :: [r] -> r -> l -> [| vl -> v -> vr |]
--    [r] \subseteq (pD r l) \wedge
--     |- vl : l \wedge
--     |- v : (pd r l) \wedge
--     |- vr : r 
injS :: [Re] -> Re -> Sym -> Q Exp
injS [r'] r l = [| \vl v -> $(injE r' r l) vl v |] 
injS (r':rs') r l = [| \vl v -> case v of 
                        { Left v -> $(injE r' r l) vl v
                        ; Right v -> $(injS rs' r l) vl v 
                        }
                     |]
-- Being different from popl'14 submission: 
-- this is required because of the splice is required eeven thought it is never caleld.                    
injS [] _ _ = [| error "injS is given an empty list" |] 



-- isEmpty :: r -> [| v -> Bool |]
--  |-  v : r

isEmpty :: Re -> Q Exp 
isEmpty (Star r) = [| \ v -> case v of { [] -> True 
                                       ; xs@(_:_) -> all $(isEmpty r) xs } |]  -- to handle case, isEmpty (Star (Choice A ())) [Right ()] -- todo: fix popl14 draft
isEmpty (Pair r1 r2) = [| \v -> case v of { (v1,v2) -> $(isEmpty r1) v1 && $(isEmpty r2) v2 }|]
isEmpty (Choice r1 r2) = [| \ v -> case v of { Left v -> $(isEmpty r1) v 
                                             ; Right v -> $(isEmpty r2) v 
                                             }
                          |]
isEmpty (L _) = [| \v -> False |]                         
isEmpty Eps = [| \() -> True |]
isEmpty Phi = [| \_ -> False |] -- why we need this?



-- projE :: r' -> r -> l -> [| vr -> Maybe (vl, vr') |]
--  |- r' \in pD r l \wedge
--  |- vl : l \wedge
--  |- vr' : r' \wedge
--  |- vr : r

projE :: Re -> Re -> Sym -> Q Exp
projE (Pair r' r'') (Star r) l = 
--  let io = unsafePerformIO (print (Pair r' r'') >> print (Star r) >> print l >> print "\n") 
--  in io `seq`
  [| \ v -> case dropWhile $(isEmpty r) v of -- we need to drop all empty element first, e.g. projE ((),Star (Choice A ())) (Star (Choice A ())) [Right (), Left A]
      { [] -> Nothing
      ; (v:vs) -> case ($(projE r' r l) v) of 
        { Nothing -> Nothing 
        ; Just (vl, v') -> Just (vl, (v',vs))
        }
      }
   |]  -- todo: fix popl14 draft
projE r' (Pair r1 r2) l  -- does not work: consider projE ((),(A|())*) (A|(), (A|())*) (Left A,[]). Since ((),(A|())*) \in (A|(), (A|())*) / A and ((), (A|())*) \in (A|()*) / A, the first case is satisfied, however Left A is not empty. --todo : fix popl14 draft
  {-
  | [] == (pD r1 l) && r' `elem` pD r2 l && posEps r1  = -- it is impossible to extract l from r1
  let io = unsafePerformIO (print r' >> print (Pair r1 r2) >> print l >> print "\n") 
  in io `seq`    
    [| \ (v1,v2) -> if $(isEmpty r1) v1
                    then $(projE r' r2 l) v2
                    else Nothing
     |] 
  -}
  | r' `elem` pD r2 l && posEps r1 =  --  it is possible to extract l from r1 or from r2
--   let io = unsafePerformIO (print r' >> print (Pair r1 r2) >> print l >> print "\n") 
--  in io `seq`    
    case r' of 
      Pair r1' r2' 
        | r1' `elem` pD r1 l ->  -- r1',r2' is derived from (r1/l)
          [| \ (v1,v2) -> if $(isEmpty r1) v1
                          then $(projE r' r2 l) v2
                          else case $(projE r1' r1 l) v1 of
                            { Just (vl, v1') -> Just (vl, (v1', v2))
                            ; Nothing -> Nothing 
                            }
           |]
      _ ->            
        [| \ (v1,v2) -> if $(isEmpty r1) v1
                        then $(projE r' r2 l) v2
                        else Nothing
         |]   
  | otherwise = 
--  let io = unsafePerformIO (print r' >> print (Pair r1 r2) >> print l >> print "\n") 
--  in io `seq`    
      case r' of 
        Pair r1' r2'  | r1' `elem` pD r1 l -> 
          [| \ (v1,v2) -> case $(projE r1' r1 l) v1 of 
              { Just (vl, v1') -> Just (vl, (v1',v2))
              ; Nothing -> Nothing 
              } 
           |]
        _ -> [| \_ -> Nothing |]
projE r' (Choice r1 r2) l         
  -- we need this case to handle proj A (A|A) (Right A)
  | r' `elem` pD r1 l &&  
    r' `elem` pD r2 l = [| \ v -> case v of 
                            { (Left v') -> $(projE r' r1 l) v' 
                            ; (Right v') -> $(projE r' r2 l) v' 
                            } |] 
  | r' `elem` pD r1 l = [| \ v -> case v of 
                            { (Left v') -> $(projE r' r1 l) v' 
                            ; (Right _) -> Nothing 
                            } |] 
  | r' `elem` pD r2 l = [| \v -> case v of 
                            { (Right v') -> $(projE r' r2 l) v' 
                            ; (Left _) -> Nothing 
                            } |] 

                        
projE Eps (L l) l'                                                 
  | l == l' = [| \vl -> Just (vl, ()) |]
projE r1 r2 l = error $ show r1 ++" not in " ++ show r2 ++ "/" ++ show l


-- projS :: [r] -> r -> l -> [| v -> Maybe (vl, v') |]
--  |- [r] \subseteq pD r l 
--  |- v : r
--  |- v' : pd r l
--  |- vl : l

projS :: [Re] -> Re -> Sym -> Q Exp
projS [] r l = [| \v -> Nothing |]
projS [r'] r l = [| \v -> $(projE r' r l) v |]
projS (r':rs') r l = [| \v -> case $(projE r' r l) v of 
                         { Just (vl, v') -> Just (vl, Left v')
                         ; Nothing -> case $(projS rs' r l) v of 
                              { Just (vl, v') -> Just (vl, Right v')
                              ; Nothing -> Nothing 
                              }
                         } |]
                     
                     
                     
-- inj :: [l] -> r1 -> r2 -> [| v1 -> v2 |]
--  [l] \subseteq \L \wedge
--  |- r1 <= r2
--  |- v1 : r1
--  |- v2 : r2
--  the Map is the co-inductive environment
inj :: Map (Re,Re) (Q Exp) -> [Sym] -> Re -> Re -> Q Exp
inj cenv _ r1 r2  | posEps r1 && (not (posEps r2)) = do 
  { loc <- location 
  ; fail $ "subtype check fail : " ++ show r1  ++ " <= " ++ show r2
  }
inj cenv _ r1 r2  | (r1,r2) `member` cenv = cenv ! (r1,r2)
inj cenv [] r1 r2 | posEps r1 = [| \v -> if $(isEmpty r1) v
                                         then $(mkEmpty r2)
                                         else error ("inj is given an empty literal set rt " ++ $(liftString $ show r1) ++ " <=" ++ $(liftString $ show r2))  |]
                  | otherwise = [| error "inj is given an empty literal set." |]
inj cenv (c:cs) r1 r2 
  -- | r1 == r2 = [| \v -> v |] 
  | isPhi r1 = [| error "inj: r1 is phi" |]
  | posEps r1 = do
    { f <- newName "inj"
    ; let cenv' = insert (r1,r2) (return (VarE f)) cenv
    ; lambE <- [| \v -> if $(isEmpty r1) v 
                        then $(mkEmpty r2)
                        else case $(projS (pD r1 c) r1 c) v of
                          { Just (vl, v) -> $(injS (pD r2 c) r2 c) vl ($(inj cenv' (c:cs) (pd r1 c) (pd r2 c)) v)
                          ; Nothing      -> $(inj cenv cs r1 r2) v
                          }
                |]
    -- the following is to generate [| let f = lambE in f |]
    ; return (LetE [(ValD (VarP f) (NormalB lambE) [])] (VarE f))
    }
  | otherwise = do 
    { f <- newName "inj"
    ; let cenv' = insert (r1,r2) (return (VarE f)) cenv
    ; lambE <- [| \v -> case $(projS (pD r1 c) r1 c) v of
                          { Just (vl, v) -> $(injS (pD r2 c) r2 c) vl ($(inj cenv' (c:cs) (pd r1 c) (pd r2 c)) v)
                          ; Nothing      -> $(inj cenv cs r1 r2) v
                          }
                |]
    -- the following is to generate [| let f = lambE in f |]
    ; return (LetE [(ValD (VarP f) (NormalB lambE) [])] (VarE f))
    }
                
                
-- proj :: [l] -> r1 -> r2 -> [| v2 -> Maybe v1 |]
--  [l] \subseteq \L \wedge
--  |- r1 <= r2
--  |- v1 : r1
--  |- v2 : r2
--  the Map is the co-inductive environment                
                
proj ::  Map (Re,Re) (Q Exp) -> [Sym] -> Re -> Re -> Q Exp                
proj cenv _ r1 r2 | posEps r1 && (not (posEps r2)) = fail $ "subtype check fail : " ++ show r1  ++ " <= " ++ show r2
proj cenv _ r1 r2 | (r1,r2) `member` cenv = cenv ! (r1,r2)
proj cenv [] r1 r2 | posEps r1 = [| \v -> if $(isEmpty r2) v 
                                          then Just $(mkEmpty r1)
                                          else error "proj is given an empty literal set" |]
                   | otherwise =  [| error "proj is given an empty literal set"|]
proj cenv (c:cs) r1 r2 
  | isPhi r1 = [| \v -> Nothing |]
  -- | r1 == r2 = [| \v -> Just v |]
  | posEps r1 = do 
    { f <- newName "proj"
    ; let cenv' = insert (r1,r2) (return (VarE f)) cenv
    ; lambE <- 
      [| \v -> if $(isEmpty r2) v 
               then Just $(mkEmpty r1)
               else case $(projS (pD r2 c) r2 c) v of 
                 { Just (vl,v) -> case $(proj cenv' (c:cs) (pd r1 c) (pd r2 c)) v of 
                      { Just v' -> Just ($(injS (pD r1 c) r1 c) vl v') 
                      ; Nothing -> Nothing 
                      }
                 ; Nothing      -> $(proj cenv cs r1 r2) v
                 }
       |]
    ; return (LetE [(ValD (VarP f) (NormalB lambE) [])] (VarE f))
    }
  | otherwise =  do  
    { f <- newName "proj"
    ; let cenv' = insert (r1,r2) (return (VarE f)) cenv
    ; lambE <- 
      [| \v -> if $(isEmpty r2) v
               then Nothing
               else case $(projS (pD r2 c) r2 c) v of 
                 { Just (vl,v) -> case $(proj cenv' (c:cs) (pd r1 c) (pd r2 c)) v of 
                      { Just v' -> Just ($(injS (pD r1 c) r1 c) vl v') 
                      ; Nothing -> Nothing 
                      }
                 ; Nothing      -> $(proj cenv cs r1 r2) v
                 }
       |]
    ; return (LetE [(ValD (VarP f) (NormalB lambE) [])] (VarE f))
    }
                     
                 
                 
                 
