{-# LANGUAGE MultiParamTypeClasses,TemplateHaskell,QuasiQuotes #-}

module Language.XHaskell.LocalTypeInference where

import Data.List (nub)
import qualified Data.Map as M
import qualified Data.Traversable as Trvsbl (mapM)
import Control.Monad
import System.IO.Unsafe


import qualified Language.Haskell.TH as TH
import qualified Language.XHaskell.Source as S 
import qualified Language.XHaskell.Target as T 

-- an implementation of B.C Pierce and D. N. Turner's local type inference

data SubtypeConstr = STC { lb :: TH.Type, var :: TH.Name, up :: TH.Type } deriving Show

bot = TH.ConT (TH.mkName "Phi")
top = TH.AppT (TH.ConT (TH.mkName "Star")) (TH.ConT (TH.mkName "."))

isBot (TH.ConT n) = TH.nameBase n == "Phi"
isBot t = False

isTop (TH.AppT (TH.ConT op) (TH.ConT n)) = TH.nameBase op == "Star" && TH.nameBase n == "."
isTop t = False

isect :: [TH.Name] -> [TH.Name] -> [TH.Name] 
isect vs vs' = filter (\v -> v `elem` vs') vs


-- variable elimination via promotion and demotion
promote :: [TH.Name] -> TH.Type -> TH.Type
promote vs (TH.VarT n) | n `elem` vs = top
promote vs t = t

demote :: [TH.Name] -> TH.Type -> TH.Type
demote vs (TH.VarT n) | n `elem` vs = bot
demote vs t = t                      

  

genSubtypeConstrs :: [TH.Name] -> -- target variables, the variable that we want to find the type substitution
                     [TH.Name] -> -- bound variables which are introduce along the way
                     TH.Type -> TH.Type -> [SubtypeConstr]
--  \bar{a}, \bar{b} |- t <: \sigma* ==> { }  -- not in used
genSubtypeConstrs vars bvars t (TH.AppT (TH.ConT op) (TH.ConT n)) 
  | TH.nameBase n == "." && TH.nameBase op == "Star"          = [] 

--  \bar{a} |- \phi <: t  ==> { }    -- not in used
genSubtypeConstrs vars bvars (TH.ConT n) t | TH.nameBase n == "Phi" = []

{-
  a \not \in \bar{a}
------------------------------------
 \bar{a}, \bar{b} |- a <: a ===> { }
-}
genSubtypeConstrs vars bvars (TH.VarT n) (TH.VarT n') | not (n `elem` vars) && (n == n') = []

{-
   a \in \bar{a}  
   fv(t) \cap \bar{a} = { }
   t \demote^{\bar{b}} t'
---------------------------------
 \bar{a}. \bar{b} |-  a <: t  ==> { \phi <: a <: t }

-}
genSubtypeConstrs vars bvars (TH.VarT n) t2 | n `elem` vars && null ((T.typeVars t2) `isect` vars) = 
  let t2' = demote bvars t2 
  in [ STC bot n t2' ] 

{-                              
   a \in \bar{a}  
   fv(t) \cap \bar{a} = { } 
   t \promote^{\bar{b}} t'
---------------------------------
 \bar{a}, \bar{b} |-  t <: a  ==> { t <: a <: \sigma* }
-}
genSubtypeConstrs vars bvars t1 (TH.VarT n) | n `elem` vars && null ((T.typeVars t1) `isect` vars) = 
  let t1' = promote bvars t1
  in [ STC t1' n top ]
{- 
 \bar{a}, \bar{b} |- t3 <: t1 ==> D1 
 \bar{a}, \bar{b} |- t2 <: t4 ==> D2
------------------------------------
 \bar{a}, \bar{b} |- t1 -> t2  <: t3 -> t4 ==> D1 ++ D2
-}
genSubtypeConstrs vars bvars (TH.AppT (TH.AppT TH.ArrowT t1) t2) (TH.AppT (TH.AppT TH.ArrowT t3) t4) = 
  genSubtypeConstrs vars bvars t3 t1 ++ genSubtypeConstrs vars bvars t2 t4
{- 
 \bar{a}, \bar{b} |- t1 <: t3 ==> D1 
 \bar{a}, \bar{b} |- t2 <: t4 ==> D2
------------------------------------
 \bar{a}, \bar{b} |- t1 | t2  <: t3 |  t4 ==> D1 ++ D2
-}
genSubtypeConstrs vars bvars (TH.AppT (TH.AppT (TH.ConT n) t1) t2) (TH.AppT (TH.AppT (TH.ConT n') t3) t4) 
  | n == n' && TH.nameBase n == "Choice" = 
    genSubtypeConstrs vars bvars t1 t3 ++ genSubtypeConstrs vars bvars t2 t4
{- 
 \bar{a}, \bar{b} |- t1 <: t3 ==> D1 
 \bar{a}, \bar{b} |- t2 <: t4 ==> D2
------------------------------------
 \bar{a} |- t1t2  <: t3t4 ==> D1 ++ D2
-}
  | n == n' && TH.nameBase n == "," = 
    genSubtypeConstrs vars bvars t1 t3 ++ genSubtypeConstrs vars bvars t2 t4
{- 
 \bar{a}, \bar{b} |- t1 <: t2 ==> D
------------------------------------
 \bar{a}, \bar{b} |- t1*  <: t2* ==> D
-}
genSubtypeConstrs vars bvars (TH.AppT (TH.ConT n) t1) (TH.AppT (TH.ConT n') t2) 
  | n == n' && TH.nameBase n == "Star" = genSubtypeConstrs vars bvars t1 t2
{-
 \bar{a}, \bar{b} |- ()  <: () ==> {}
-}
genSubtypeConstrs vars bvars (TH.ConT n) (TH.ConT n')
  | n == n' && TH.nameBase n == "()" = []
{-
------------------------------------
 \bar{a} |- l  <: l ==> {}
-}
  | TH.nameBase n == TH.nameBase n' = []
genSubtypeConstrs vars bvars t1 (TH.ForallT tvbs cxt t2) =  -- todo : what to do with cxt?
  let bvars' = bvars ++ nub (map T.getTvFromTvb tvbs)
  in genSubtypeConstrs vars bvars' t1 t2     
genSubtypeConstrs vars bvars (TH.ForallT tvbs cxt t1) t2 =  -- todo : what to do with cxt?
  let bvars' = bvars ++ nub (map T.getTvFromTvb tvbs)
  in genSubtypeConstrs vars bvars' t1 t2     

genSubtypeConstrs vars bvars t1 t2 = [] -- error $ "failed to generate subtype constraints " ++ show vars ++ " " ++ show t1 ++  " " ++ show t2        

solveSubtypeConstrs :: [SubtypeConstr] -> TH.Type -> TH.Q T.Subst 
solveSubtypeConstrs constrs r = 
  -- create a map mapping var -> [ constraint ]
  let cdict = foldl (\m c@(STC l v u) -> case M.lookup v m of
                        { Just cs -> M.update (\_ -> Just (c:cs)) v m 
                        ; Nothing -> M.insert v [c] m }) M.empty constrs
      -- collapse constraints for the same variable based on 
  in do 
    { cdict' <- Trvsbl.mapM collapseConstrs cdict 
    ; subst  <- Trvsbl.mapM (findMinSubst r) cdict'
    ; return subst 
    }
     
     
collapseConstrs :: [SubtypeConstr] -> TH.Q SubtypeConstr
collapseConstrs [] = fail "the collapseConstrs is given an empty list"
collapseConstrs (c:cs) = 
  foldM (\(STC l v u) (STC l' v' u') -> do -- precondition, v == v'
           { l'' <- upperBound l l'
           ; u'' <- lowerBound u u' 
           ; return (STC l'' v u'')}) c cs
    where upperBound t1 t2 | t1 == t2 = return t1
                           | isBot t1 = return t2
                           | isBot t2 = return t1
                           | isTop t1 = return t1
                           | isTop t2 = return t2
                           | otherwise = fail $ "can't decide the upper bound of " ++ (TH.pprint t1) ++ " and " ++ (TH.pprint t2) -- todo subtyp relation?
          lowerBound t1 t2 | t1 == t2 = return t1
                           | isBot t1 = return t1
                           | isBot t2 = return t2
                           | isTop t1 = return t2
                           | isTop t2 = return t1
                           | otherwise = fail $ "can't decide the lower bound of " ++ (TH.pprint t1) ++ " and " ++ (TH.pprint t2)
          
                          
findMinSubst :: TH.Type -> SubtypeConstr -> TH.Q TH.Type
findMinSubst r (STC l v u) 
  | v `constant` r || v `covariant` r = return l
  | v `contravariant` r = return u
  | v `invariant` r && l == u = return l
  | otherwise = fail ("unable to find minimal substitution given type " ++ TH.pprint r ++ " and bounds " ++ TH.pprint l ++ "<:" ++ TH.pprint v ++ "<:" ++ TH.pprint u)
  
                              
     
constant :: TH.Name -> TH.Type -> Bool
constant n t = not (n `elem` (T.typeVars t))

covariant :: TH.Name -> TH.Type -> Bool
covariant n t = n `elem` (T.coTypeVars t)

contravariant :: TH.Name -> TH.Type -> Bool
contravariant n t = n `elem` (T.contraTypeVars t)

invariant :: TH.Name -> TH.Type -> Bool
invariant n t = n `elem` (T.contraTypeVars t) && 
                n `elem` (T.coTypeVars t)
