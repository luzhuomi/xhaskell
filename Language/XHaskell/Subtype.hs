module Language.XHaskell.Subtype where

import qualified Data.Map as M
import qualified Language.Haskell.TH as TH  
import Language.Haskell.Exts.Syntax

import Language.XHaskell.Error
import Language.XHaskell.TypeSpec
  
-- t1 <= t2
class Subtype t1 t2 where
  dcast :: SrcLoc -> t1 -> t2 -> TH.Q TH.Exp
  ucast :: SrcLoc -> t1 -> t2 -> TH.Q TH.Exp



instance Subtype TH.Type TH.Type where  
  -- allow upcast among function types
  {-
    |- t3 <= t1 ~> u1
    |- t2 <= t4 ~> u2
  ----------------------------------------
   |- t1 -> t2 <= t3 -> t4 ~> \f -> \x -> u2 (f (u1 x))
  -}
  ucast srcLoc (TH.AppT (TH.AppT TH.ArrowT t1) t2) (TH.AppT (TH.AppT TH.ArrowT t3) t4) = do 
    { u1 <- ucast srcLoc t3 t1
    ; u2 <- ucast srcLoc t2 t4
    ; return (TH.LamE [TH.VarP (TH.mkName "f"), TH.VarP (TH.mkName "x")] 
              (TH.AppE u2 (TH.AppE (TH.VarE $ TH.mkName "f") (TH.AppE u1 (TH.VarE $ TH.mkName "x")))))
    }
  ucast srcLoc  t1 t2 = do  
    { let r1 = toRE t1
          r2 = toRE t2
          s  = sig (Choice r1 r2) -- get syms from r1 and r2
          
    -- ; TH.runIO (putStrLn $ TH.pprint t1 ++ " <= " ++ TH.pprint t2 ++ " with sig = " ++ show s)
    -- ; TH.runIO (putStrLn $ show r1 ++ " <= " ++ show r2)
    ; TH.recover 
      (failWithSrcLoc srcLoc ("Subtyping failed:" ++ TH.pprint t1 ++ " <= " ++ TH.pprint t2) )
      (inj M.empty s r1 r2)
    -- ; return (TH.VarE (TH.mkName $ "ucast_" ++ show r1 ++ "<=" ++ show r2)) -- for debugging
    }
  dcast srcLoc t1 t2 = do 
    { let r1 = toRE t1
          r2 = toRE t2
          s  = sig (Choice r1 r2)
    -- ; TH.runIO (putStrLn $ TH.pprint t1 ++ " <= " ++ TH.pprint t2 ++ " with sig = " ++ show s)
    ; TH.recover 
      (failWithSrcLoc srcLoc ("Subtyping failed:" ++ TH.pprint t1 ++ " <= " ++ TH.pprint t2) )
      (proj M.empty s r1 r2)
    -- ; return (TH.VarE (TH.mkName $ "dcast_" ++ show r1 ++ "<=" ++ show r2)) -- for debuggin         
    }
    

-- | convert a TH.type to a regular expression. Skolemizing type vars and (non-regex) type constructors
toRE :: TH.Type -> Re 
toRE (TH.AppT (TH.ConT n) t) 
  | TH.nameBase n == "Star" = Star (toRE t)
toRE (TH.AppT (TH.AppT (TH.ConT n) t1) t2) 
  | TH.nameBase n == "Choice" = Choice (toRE t1) (toRE t2)
toRE (TH.AppT (TH.AppT (TH.TupleT 2) t1) t2) = Pair (toRE t1) (toRE t2)
toRE (TH.ConT n)                               
  | TH.nameBase n == "()" = Eps
  | TH.nameBase n == "Phi" = Phi
  | otherwise = L (TH.nameBase n) -- todo: fixme, this is a hack to get GHC.Types.Bool translated to "Bool", otherwise we can't handle GHC.Types.Bool <= Bool
toRE (TH.TupleT 0) = Eps                            

toRE t = L (TH.pprint (removeQual t)) -- todo: we should add the qualifiers instead of removing them.

removeQual :: TH.Type -> TH.Type               
removeQual (TH.ConT n) = TH.ConT (TH.mkName (TH.nameBase n))
removeQual (TH.AppT t1 t2) = TH.AppT (removeQual t1) (removeQual t2)
removeQual (TH.ForallT tvbs cxt t) = TH.ForallT tvbs cxt (removeQual t)
removeQual (TH.TupleT p) = TH.TupleT p
removeQual (TH.VarT n) = TH.VarT n
removeQual TH.ListT = TH.ListT
removeQual TH.ArrowT = TH.ArrowT
removeQual (TH.SigT t k) = TH.SigT (removeQual t) k


