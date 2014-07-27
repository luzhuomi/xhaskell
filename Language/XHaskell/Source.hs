module Language.XHaskell.Source where


import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Syntax
import Language.Haskell.Exts.Extension
import Language.Haskell.Exts.Pretty
import Data.List


-- | XHaskell parse mode

xhPm = defaultParseMode{extensions = [EnableExtension ScopedTypeVariables, EnableExtension FunctionalDependencies, EnableExtension MultiParamTypeClasses, EnableExtension RecordPuns]}



isStar :: QName -> Bool
isStar (Qual (ModuleName mn) (Ident "Star")) = True
isStar (UnQual (Ident "Star")) = True
isStar _ = False

isChoice :: QName -> Bool
isChoice (Qual (ModuleName mn) (Ident "Choice")) = True
isChoice (UnQual (Ident "Choice")) = True
isChoice _ = False

isPair :: QName -> Bool
isPair (Qual (ModuleName mn) (Ident "Pair")) = True
isPair (UnQual (Ident "Pair")) = True
isPair _ = False

isEps :: QName -> Bool
isEps (Qual (ModuleName mn) (Ident "Eps")) = True
isEps (UnQual (Ident "Eps")) = True
isEps _ = False

isTypeSig :: Decl -> Bool 
isTypeSig (TypeSig srcLoc idents ty) = True
isTypeSig _                          = False

isFunBind :: Decl -> Bool
isFunBind (FunBind matches) = True
isFunBind _                 = False


isClassDecl :: Decl -> Bool 
isClassDecl (ClassDecl srcLoc ctxt name tyVars fds classDecls) = True
isClassDecl _                                                  = False

isInstDecl :: Decl -> Bool
isInstDecl (InstDecl srcLoc ctxt name tyVars instDecls) = True
isInstDecl _                                            = False


isDtDecl :: Decl -> Bool
isDtDecl (DataDecl srcLoc dataOrNew context dtName tyVarBinds qualConDecls derivings) = True
isDtDecl _                                                                            = False

isMono :: Type -> Bool
isMono t@(TyForall Nothing ctxt ty) = null (typeVars t)
isMono (TyForall (Just _) ctxt ty) = False
isMono t = null (typeVars t)

isPoly :: Type -> Bool
isPoly t = not (isMono t)

addQualifier :: Type -> Type
addQualifier t = let tvs = nub $ sort (typeVars t)
                     tvbs' = map UnkindedVar tvs
                 in case t of 
                   { TyForall (Just tvbs) ctxt ty -> 
                        let tvs' = map getTvFromTvb tvbs
                        in TyForall (Just $ tvbs ++ map UnkindedVar (filter (\x -> not (elem x tvs')) tvs)) ctxt ty
                   ; TyForall Nothing ctxt ty -> TyForall (Just tvbs') ctxt ty 
                   ; t -> TyForall (Just tvbs') [] t
                   }

typeVars :: Type -> [Name]
typeVars = nub . sort . typeVars'

typeVars' :: Type -> [Name]
typeVars' (TyForall Nothing ctxt ty) = typeVars' ty --todo ctxt?
typeVars' (TyForall (Just tvbs) ctxt ty) = 
  let fvs   = typeVars' ty
      names = map getTvFromTvb tvbs
      isNotFree name = name `elem` names
  in filter (not . isNotFree) fvs
typeVars' (TyFun t1 t2) = typeVars' t1 ++ typeVars' t2  
typeVars' (TyTuple boxed ts) = concatMap typeVars' ts
typeVars' (TyList ty) = typeVars' ty
typeVars' (TyApp t1 t2) = typeVars' t1 ++ typeVars' t2
typeVars' (TyVar n) = [n]
typeVars' (TyCon _)  = []
typeVars' (TyParen ty) = typeVars' ty
typeVars' (TyInfix t1 qname t2) = typeVars' t1 ++ typeVars' t2
typeVars' (TyKind ty k) = typeVars' ty
     
                          
getTvFromTvb :: TyVarBind -> Name
getTvFromTvb (UnkindedVar v) = v
getTvFromTvb (KindedVar v k) = v


unbang :: BangType -> Type
unbang (UnBangedTy t) = t
unbang (BangedTy t) = t




-- remove the structure of the nested function application
-- (((f e1) e2) 3)  ===>  [f,e1,e2,e3]
flatten :: Exp -> [Exp]
flatten (App e e') = (flatten e) ++ [e']
flatten e = [e]

