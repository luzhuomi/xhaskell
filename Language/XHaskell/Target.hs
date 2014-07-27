module Language.XHaskell.Target where

import Language.Haskell.TH as TH
import qualified Language.Haskell.Exts.Syntax as HSX
import qualified Data.Map as M
import Control.Monad.State.Lazy 
import Data.List 


import Language.XHaskell.TypeSpec 
import Language.XHaskell.Error 
import Language.XHaskell.Subtype

-- | return all the type variable names from the type
typeVars :: Type -> [Name]
typeVars = nub . sort . typeVars'

typeVars' :: Type -> [Name]
typeVars' (VarT n) = [n]
typeVars' (ForallT tyVarBnds cxt t) = 
  let inScoped = map (\b -> case b of {PlainTV n -> n; KindedTV n k -> n}) tyVarBnds
      free = typeVars' t
  in filter (\n -> not (n `elem` inScoped)) free
typeVars' (ConT _) = []
typeVars' (TupleT _) = []
typeVars' ArrowT = []
typeVars' ListT = []
typeVars' (AppT t1 t2) = typeVars' t1 ++ typeVars' t2
typeVars' (SigT t k) = typeVars' t

-- | return all the co-variant type variable names from the type
coTypeVars :: Type -> [Name]
coTypeVars = nub. sort . coTypeVars'                        

coTypeVars' :: Type -> [Name]
coTypeVars' (VarT n) = [n]
coTypeVars' (ForallT tyVarBnds cxt t) = 
  let inScoped = map (\b -> case b of {PlainTV n -> n; KindedTV n k -> n}) tyVarBnds
      free = coTypeVars' t
  in filter (\n -> not (n `elem` inScoped)) free
coTypeVars' (ConT _) = []
coTypeVars' (TupleT _) = []
coTypeVars' ArrowT = []
coTypeVars' ListT = []
coTypeVars' (AppT (AppT ArrowT t1) t2) = coTypeVars' t2
coTypeVars' (AppT t1 t2) = coTypeVars' t1 ++ coTypeVars' t2
coTypeVars' (SigT t k) = coTypeVars' t
     
     
-- | return all the contra-variant type variable names from the type
contraTypeVars :: Type -> [Name]
contraTypeVars = nub. sort . contraTypeVars'                        

contraTypeVars' :: Type -> [Name]
contraTypeVars' (VarT n) = [n]
contraTypeVars' (ForallT tyVarBnds cxt t) = 
  let inScoped = map (\b -> case b of {PlainTV n -> n; KindedTV n k -> n}) tyVarBnds
      free = contraTypeVars' t
  in filter (\n -> not (n `elem` inScoped)) free
contraTypeVars' (ConT _) = []
contraTypeVars' (TupleT _) = []
contraTypeVars' ArrowT = []
contraTypeVars' ListT = []
contraTypeVars' (AppT (AppT ArrowT t1) t2) = contraTypeVars' t1 
contraTypeVars' (AppT t1 t2) = contraTypeVars' t1 ++ contraTypeVars' t2
contraTypeVars' (SigT t k) = contraTypeVars' t

-- | create fresh names of the variables for poly type 
renameVars :: Type -> Q Type 
renameVars (ForallT tvbs ctxt t) = do
  { let vars = map getTvFromTvb tvbs
  ; ps <- mapM (\n -> do
                   { n' <- newName (nameBase n)
                   ; return (n, n')
                   }) vars
  ; let subst = M.fromList (map (\(f,s) -> (f, VarT s)) ps)
        tvb'  = map (PlainTV . snd) ps
  ; return (ForallT tvb' (applySubst subst ctxt) (applySubst subst t))
  }
renameVars t = return t

-- | test isomorphism among two types
isomorphic :: Type -> Type -> Bool
isomorphic t1 t2 =
  case (t1,t2) of 
    { (ForallT tvb1 cxt1 t1', ForallT tvb2 cxt2 t2') -> 
         if (not ((length tvb1) == (length tvb2)))
         then False
         else 
           let tv1 = map getTvFromTvb tvb1
               tv2 = map getTvFromTvb tvb2
               subst2 = M.fromList (zip tv2 (map VarT tv1)) 
           in ( cxt1 == (applySubst subst2 cxt2) ) &&
              ( t1' == (applySubst subst2 t2') )
    ; (_,_) -> t1 == t2
    }


-- | test whether a type is monomorphic
isMono :: Type -> Bool
isMono (ForallT tyVarBnds cxt ty) = null tyVarBnds
isMono t = True -- null (typeVars t)

isPoly :: Type -> Bool
isPoly = not . isMono


-- | return variable names from type variable binder
getTvFromTvb :: TyVarBndr -> Name
getTvFromTvb (PlainTV n) = n
getTvFromTvb (KindedTV n _ ) = n



-- | type substitution mapping names to types
type Subst = M.Map Name Type 

-- | state evironment
data Env = Env { freeVars :: [Name]
               , subst :: Subst 
               }


isFree :: Name -> Env -> Bool
isFree n env = n `elem` (freeVars env)

-- | lookup the type from the type substitution
getSubst :: Name -> Env -> Maybe Type
getSubst n env = M.lookup n (subst env)

addSubst :: Name -> Type -> Env -> Env
addSubst n t env = env{subst =  M.insert n t (subst env)}


findSubst :: Type -- ^ poly type
             -> Type  -- ^ mono type
             -> Maybe Subst
findSubst (ForallT tyVarBnds cxt t) t' =  
  case runState  (findSubst' t t') (Env fvs M.empty) of
    (True, env) -> Just (subst env)
    (False, _ ) -> Nothing
  where fvs = map getTvFromTvb tyVarBnds




-- this type looks a bit weird, maybe a maybe monad will work
findSubst' :: Type -> Type -> State Env Bool
findSubst' (VarT n) t = do 
  { env <- get  
  ; if n `isFree` env 
    then case (getSubst n env) of
      { Just t' -> return (t' == t)
      ; Nothing -> let env' = addSubst n t env
                   in do { put env
                         ; return True 
                         }
      }
    else case t of 
      { VarT n' -> return (n == n')
      ; _       -> return False 
      }
  }
findSubst' (ConT n1) (ConT n2) = return (nameBase n1 == nameBase n2)  -- todo: incorporate the qualifier.
findSubst' (TupleT i) (TupleT j) = return (i == j)
findSubst' ArrowT ArrowT = return True
findSubst' ListT ListT = return True
findSubst' (AppT t1 t2) (AppT t3 t4) = do 
  { bool <- findSubst' t1 t3
  ; if bool 
    then findSubst' t2 t4
    else return False 
  }
findSubst' _ _ = return False                                       
             
-- | apply the substitution to a type or a context             
class Substitutable a where
  applySubst :: Subst -> a -> a
  
  
  
instance Substitutable Type where
  applySubst subst (VarT n) = 
    case M.lookup n subst of
      { Nothing -> VarT n
      ; Just t  -> t
      }
  applySubst subst (ConT n) = ConT n
  applySubst subst (TupleT i) = TupleT i
  applySubst subst ArrowT = ArrowT                              
  applySubst subst ListT = ListT
  applySubst subst (AppT t1 t2) = AppT (applySubst subst t1) (applySubst subst t2)
  applySubst subst (ForallT tyVarBnds cxt t) = 
    let dom = M.keys subst
        tvbs = filter (\tyVarBnd -> case tyVarBnd of
                          { PlainTV n -> not (n `elem` dom)
                          ; KindedTV n k -> not (n `elem` dom) 
                          }) tyVarBnds
    in ForallT tvbs (applySubst subst cxt) (applySubst subst t)
  
  
instance Substitutable a => Substitutable [a] where  
  applySubst s xs = map (applySubst s) xs
  
-- | apply Substition to context and build a set of constraints
instance Substitutable Pred where
  applySubst s (ClassP name ts) = ClassP name (map (applySubst s) ts)
  applySubst s (EqualP t1 t2)   = EqualP (applySubst s t1) (applySubst s t2)
  



-- t is a func type like t1 -> t2 -> ... -> tn
-- ts is a list of types t1, t2, ... , tn-1
-- matches ts with t returning tn
lineUpTypes :: HSX.SrcLoc -> Type -> [Type] -> Q Type
lineUpTypes srcLoc t [] = return t
lineUpTypes srcLoc (ForallT tvb cxt t) ts = lineUpTypesP srcLoc tvb t ts
lineUpTypes srcLoc  t@(AppT (AppT ArrowT t1) t2) ts =  -- mono
  let ts' = argsTypes (AppT (AppT ArrowT t1) t2)
  in if length ts' == length ts 
     then do 
       { succ <- lineUpTypesM srcLoc ts' ts 
       ; if succ 
         then return t2 
         else failWithSrcLoc srcLoc  $ "unable to line up arg types '" ++ pprint ts' ++ "' with types '" ++ pprint ts ++ "'"
       }
     else failWithSrcLoc srcLoc  $ "unable to line up arg types '" ++ pprint ts' ++ "' with types '" ++ pprint ts ++ "'"
lineUpTypes srcLoc t ts = failWithSrcLoc srcLoc  $ "unable to line up type " ++ pprint t ++ " with types " ++ pprint ts


lineUpTypesM :: HSX.SrcLoc -> [Type] -> [Type] -> Q Bool
lineUpTypesM srcLoc [] [] = return True
lineUpTypesM srcLoc (t:ts) (r:rs) | t == r = lineUpTypesM srcLoc ts rs
                                  | otherwise = do { u <- ucast srcLoc  r t 
                                                   ; lineUpTypesM srcLoc ts rs
                                                   }
                             

lineUpTypesP :: HSX.SrcLoc -> [TyVarBndr] -> Type -> [Type] -> Q Type
lineUpTypesP srcLoc tvbs t_@(AppT (AppT ArrowT t1) t2) ts@(_:_) = 
  let fvs = map getTvFromTvb tvbs
      t1' = foldl1 (\ta tb -> AppT (AppT ArrowT ta) tb) ts
  in case runState (findSubst' t1 t1') (Env fvs M.empty) of
    (True, env) -> let s = subst env
                   in return $ applySubst s t2
    (False, _ ) -> failWithSrcLoc srcLoc  $ "unable to line up type ." ++ show t_  ++ show ts
                    
      


-- t1 -> t2 -> ... -> tn  ~> [t1,t2,...,tn-1]
argsTypes :: Type -> [Type]
argsTypes (AppT (AppT ArrowT t1) t2) = argsTypes' t1
argsTypes t = [] -- e.g. Nil :: List a

argsTypes' :: Type -> [Type]
argsTypes' (AppT (AppT ArrowT t1) t2) = argsTypes' t1 ++ [t2]
argsTypes' t = [t]   

-- t1 -> t2 -> ... -> tn ~> tn
resultType :: Type -> Type
resultType (AppT (AppT ArrowT t1) t2) = t2
resultType t2 = t2  -- e.g Nil :: List a



-- remove the structure of the nested function application
-- (((f e1) e2) 3)  ===>  [f,e1,e2,e3]
flatten :: Exp -> [Exp]
flatten (AppE e e') = (flatten e) ++ [e']
flatten e = [e]

-- break type based on the given integer n,
-- t1 -> t2 -> ... -> tn   and 3 ~> ([t1,t2,t3], t4 -> ... -> tn)
breakFuncType :: Type -> Int -> ([Type],Type)
breakFuncType t 0 = ([],t)
breakFuncType (AppT (AppT ArrowT t1) t2) n = 
  let (ts,t) = breakFuncType t2 (n-1) 
  in (t1:ts,t)
breakFuncType t _ = ([],t)     


--


newNames :: Int -> String -> Q [Name]
newNames 0 _ = return []
newNames i s = do 
  { n  <- newName s 
  ; ns <- newNames (i-1) s
  ; return (n:ns)
  }


-- | translate XHaskell type in TH representation to Haskell in TH representation
xhTyToHsTy :: TH.Type -> TH.Type
xhTyToHsTy (TH.ForallT tVarBindings ctxt t) = TH.ForallT tVarBindings ctxt $ xhTyToHsTy t
xhTyToHsTy (TH.VarT n) = TH.VarT n
xhTyToHsTy (TH.ConT n) | TH.nameBase n == "Star" = TH.ListT
                       | TH.nameBase n == "Choice" = TH.ConT (TH.mkName "Either")
                       -- | TH.nameBase n == "Eps"    = TH.TupleT 0 -- todo: or  TH.ConT (TH.mkName "()") -- Eps never appears in the source language
                       | otherwise                 = TH.ConT n
xhTyToHsTy (TH.TupleT i) = TH.TupleT i
xhTyToHsTy TH.ArrowT = TH.ArrowT
xhTyToHsTy TH.ListT = TH.ListT
xhTyToHsTy (TH.AppT t1 t2) = TH.AppT (xhTyToHsTy t1) (xhTyToHsTy t2)
xhTyToHsTy (TH.SigT t k) = TH.SigT (xhTyToHsTy t) k

