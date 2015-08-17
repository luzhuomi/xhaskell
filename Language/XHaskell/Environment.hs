{-# LANGUAGE MultiParamTypeClasses,TemplateHaskell,QuasiQuotes #-}

module Language.XHaskell.Environment where



import Data.List (zip4,sort,nub,foldl1)
import Control.Monad

import qualified Language.Haskell.TH as TH
import qualified Data.Map as M

import Language.Haskell.Exts.Syntax
import Language.Haskell.Exts.Pretty

import qualified Language.XHaskell.Source as S 
import qualified Language.XHaskell.Target as T 



-- | XHaskell Type Env
-- | maps (source language's) var name to type (target language's type AST) and set of possible record labels (only for record constructors)
-- |  we leave them in target type repr for the ease for ucast and comparison, because lookupQName uses TH.reify which emits TH.Type
type TyEnv = M.Map Name (TH.Type, [Name])
             
                     

mkTyEnv :: [Decl] -> TH.Q TyEnv
mkTyEnv decls = foldM (\tenv decl -> 
                        case decl of 
                          { TypeSig srcLoc idents ty -> do 
                               { let ty' = if S.isPoly ty then S.addQualifier ty else ty
                               ; ty'' <- translateType ty'
                               ; return $ foldl (\tenv' ident -> addTyEnv ident ty'' tenv') tenv idents 
                               }
                          ; _ -> return tenv }) M.empty decls 
                
                
addTyEnv :: Name -> TH.Type -> TyEnv -> TyEnv
addTyEnv n t tenv = case M.lookup n tenv of
  { Nothing -> M.insert n (t,[]) tenv 
  ; Just _  -> M.update (\_ -> Just (t,[])) n tenv 
  }
                    
addRecTyEnv :: Name -> TH.Type -> [Name] -> TyEnv -> TyEnv
addRecTyEnv n t ns tenv = case M.lookup n tenv of
  { Nothing -> M.insert n (t,ns) tenv 
  ; Just _  -> M.update (\_ -> Just (t,ns)) n tenv 
  }
                    
                    
unionTyEnv :: TyEnv -> TyEnv -> TyEnv             
unionTyEnv tenv1 tenv2 = M.union tenv1 tenv2 -- a left-biase union                

-- | Function (body) binding Env                
-- | maps function name to function defintions
type BdEnv = M.Map Name [Match]                

mkBdEnv :: [Decl] -> BdEnv
mkBdEnv decls = foldl (\benv decl -> 
                        case decl of
                          { FunBind matches -> foldl (\benv' m@(Match srcLoc ident pats mbTy rhs localBnds) ->
                                                       case M.lookup ident benv' of
                                                         { Just ms -> M.update (\ ms -> Just $ ms ++ [m]) ident benv' 
                                                         ; Nothing -> M.insert ident [m] benv' }
                                                     ) benv matches 
                          ; _ -> benv }) M.empty decls



-- | Type Class Env
-- | maps class name to class definition
type ClEnv = M.Map Name (SrcLoc, [Asst], [TyVarBind], [FunDep], [ClassDecl])

mkClEnv :: [Decl] -> ClEnv 
mkClEnv decls = foldl (\clEnv decl -> 
                        case decl of 
                          { ClassDecl srcLoc context name tyVars fds classDecls -> 
                               M.insert name (srcLoc,context,tyVars,fds,classDecls) clEnv 
                          ; _ -> clEnv }) M.empty decls 

-- | extract the  type bindings from the class functions
mkClTyEnv :: [Decl] -> TH.Q TyEnv 
mkClTyEnv decls = foldM (\tenv decl ->
                          case decl of
                            { ClassDecl srcLoc context clName tyVars fds classDecls ->
                                 foldM (\tenv' cdecl ->
                                         case cdecl of
                                           { ClsDecl decl@(TypeSig srcLoc fnames ty) -> 
                                                foldM (\tenv'' fname -> do
                                                        { let fv = map UnkindedVar $ S.typeVars ty
                                                              tyVars' = map (TyVar . S.getTvFromTvb) tyVars
                                                              ty' = TyForall (Just fv) [ClassA (UnQual clName) tyVars'] ty 
                                                        ; qty' <- translateType ty'
                                                        ; return $ addTyEnv fname qty' tenv''}) tenv' fnames 
                                           ; _ -> return tenv' -- todo: associated data type & type famliy 
                                           }
                                         ) tenv classDecls 
                            ; _ -> return tenv }) M.empty decls
                  
                  
-- | extract the type bindings for data type constructors
mkDtTyEnv :: [Decl] -> TH.Q TyEnv
mkDtTyEnv decls = foldM (\tenv decl ->
                          case decl of 
                            { DataDecl srcLoc dataOrNew [] dtName tyVarBinds qualConDecls derivings -> 
                                 let tvs = map (TyVar . S.getTvFromTvb) tyVarBinds
                                     rt = foldl (\t1 t2 -> TyFun t1 t2) (TyCon (UnQual dtName)) tvs
                                 in foldM (\tenv' (QualConDecl srcLoc tyVarBinds' context condecl) ->
                                            if (length tyVarBinds' == 0)
                                            then case condecl of
                                              { ConDecl dcName dtypes -> do 
                                                   { let tys = map S.unbang dtypes
                                                         ctxt = [] -- todo: get from context, NOTE we do not support context in the data type nor existential type
                                                         ty  | length tys == 0 = rt
                                                             | otherwise       = TyFun (foldl1 TyFun tys) rt
                                                         ty' | length tvs == 0 = ty
                                                             | otherwise       = TyForall (Just tyVarBinds) ctxt ty
                                                   ; qty' <- translateType ty'
                                                   ; return $ addTyEnv dcName qty' tenv'
                                                   }
                                              ; InfixConDecl bangType1 dcName bangType2 -> do
                                                   { let ty1 = S.unbang bangType1
                                                         ty2 = S.unbang bangType2
                                                         ctxt = [] -- todo: get from context
                                                         ty | length tvs == 0 = TyFun (TyFun ty1 ty2) rt
                                                            | otherwise       = TyForall (Just tyVarBinds) ctxt (TyFun (TyFun ty1 ty2) rt)
                                                   ; qty <- translateType ty
                                                   ; return $ addTyEnv dcName qty tenv'
                                                   }
                                              ; RecDecl dcName names_bangType_pairs -> do 
                                                   { nameTypes <- mapM (\ (names, bangType) -> do
                                                                           { let ty = S.unbang bangType
                                                                           ; return (map (\name -> (name, ty)) names)
                                                                           } ) names_bangType_pairs
                                                   ; let ctxt = []
                                                         names = concatMap fst names_bangType_pairs
                                                         tys = map (\ (_,ty) -> ty ) $ concat nameTypes
                                                         ty | length tvs == 0 = TyFun (foldl1 TyFun tys) rt
                                                            | otherwise       = TyForall (Just tyVarBinds) ctxt (TyFun (foldl1 TyFun tys) rt)
                                                   ; qty <- translateType ty
                                                   ; let tenv'' = addRecTyEnv dcName qty names tenv'
                                                   ; tenv''' <- foldM (\ tenv (name,ty) -> do
                                                                          { let ty' | length tvs == 0 = TyFun rt ty
                                                                                    | otherwise       = TyForall (Just tyVarBinds) ctxt (TyFun rt ty)
                                                                          ; qty <- translateType ty'
                                                                          ; return $ addTyEnv name qty tenv} ) tenv'' (concat nameTypes)
                                                   ; return tenv'''
                                                   }
                                                                                      
                                              }
                                            else fail "Existential type is not supported."  
                                          ) tenv qualConDecls
                            ; DataDecl srcLoc dataOrNew context dtName tyVarBinds qualConDecls derivings -> 
                                   fail "Data type context is not supported."
                            ; _ -> return tenv }) M.empty decls



-- | maps class name to instance definitions
type InstEnv = M.Map QName [(SrcLoc, [Asst], [Type], [InstDecl])] 


mkInstEnv :: [Decl] -> InstEnv
mkInstEnv decls = foldl (\instEnv decl ->
                          case decl of
                            { InstDecl srcLoc _ _ ctxt name ts instdecls -> 
                                 case M.lookup name instEnv of
                                   { Nothing -> M.insert name [(srcLoc, ctxt, ts, instdecls)] instEnv 
                                   ; Just _  -> M.update (\xs -> Just (xs ++ [(srcLoc, ctxt, ts, instdecls)])) name instEnv 
                                   }
                            ; _ -> instEnv 
                            }) M.empty decls 
                          


-- | uniform representation of the constraint
data Constraint = ClassC TH.Name [TH.Name]

instance Show Constraint where
  show (ClassC n names) = TH.pprint n ++ " (" ++ TH.pprint names ++ ")"


-- | constraint environment map class name to list of constraints
type ConstrEnv = M.Map TH.Name [Constraint] 


unionConstrEnv :: ConstrEnv -> ConstrEnv -> ConstrEnv
unionConstrEnv cenv1 cenv2 = M.union cenv1 cenv2

cxtToConstrs :: TH.Cxt -> [Constraint]
cxtToConstrs cxt = undefined

cxtToConstrEnv :: TH.Cxt -> ConstrEnv 
cxtToConstrEnv cxt = undefined

buildConstrEnv :: ClEnv -> InstEnv -> ConstrEnv 
buildConstrEnv = undefined


addConstrEnv :: TH.Cxt -> ConstrEnv -> ConstrEnv
addConstrEnv = undefined


-- | deducible check whether the set of constraints is deducable from the constraint environment
deducible :: [Constraint] -> ConstrEnv -> Bool
deducible _ _ = True -- undefined todo



-- | translate kind                                        
translateKind :: Kind -> TH.Q TH.Kind
translateKind KindStar = return TH.StarT
translateKind KindBang = fail "unable to handle kind !"
translateKind (KindFn k1 k2) = do 
  { qk1 <- translateKind k1
  ; qk2 <- translateKind k2 
  ; return (TH.AppT (TH.AppT TH.ArrowT qk1) qk2)
  }
translateKind (KindParen k) = translateKind k
translateKind (KindVar n) = fail "unable to handle kind variable"

-- | convert type from Haskell Src Ext Representation to TH WITHOUT performing the XHaskell to HS translation
translateType :: Type -> TH.Q TH.Type 
translateType (TyForall Nothing ctxt t) = do 
  { qt <- translateType t
  ; qctxt <- translateContext ctxt
  ; return (TH.ForallT [] qctxt qt)
  } 
translateType (TyForall (Just tvBnds) ctxt t) = do 
  { qt <- translateType t
  ; qctxt <- translateContext ctxt
  ; qtvBinds <- mapM translateTyVarBind tvBnds
  ; return (TH.ForallT qtvBinds qctxt qt)
  }
translateType (TyFun t1 t2) = do 
  { qt1 <- translateType t1
  ; qt2 <- translateType t2
  ; return (TH.AppT (TH.AppT TH.ArrowT qt1) qt2)
  }
translateType (TyTuple Unboxed ts) = fail "can't handle unboxed tupple type" -- nofix: TH does not support
translateType (TyTuple Boxed []) =  fail "empty tuple type encountered"
translateType (TyTuple Boxed [t]) = translateType t
translateType (TyTuple Boxed (t:ts)) = do -- (t1,...,tn) ~> (((t1,t2),t3), ..., tn)
  { qt  <- translateType t
  ; qts <- mapM translateType ts 
  ; return $ foldl (\t1 t2 -> TH.AppT (TH.AppT (TH.TupleT 2) t1) t2) qt qts
  }
translateType (TyList t) = do                                    
  { qt <- translateType t
  ; return (TH.AppT TH.ListT qt)
  }
translateType (TyApp t1 t2) = do                           
  { qt1 <- translateType t1
  ; qt2 <- translateType t2
  ; return (TH.AppT qt1 qt2) 
  }
translateType (TyVar name) = do                               
  { qName <- translateName name
  -- ; n <- TH.newName "a"
  ; return (TH.VarT qName)
  }
translateType (TyCon qualName) = 
  case qualName of
    { Special UnitCon -> return (TH.TupleT 0)
    ; Special ListCon -> return (TH.ConT (TH.mkName "GHC.Types.[]"))
    ; Special FunCon  -> return TH.ArrowT
    ; Special (TupleCon Unboxed _) -> fail "can't handle unboxed tupple type" -- nofix: TH does not support
    ; Special (TupleCon Boxed i)   -> return (TH.TupleT i)
    ; Special Cons                 -> fail "(:) appears in the type signature"  -- nofix
    ; Special UnboxedSingleCon     -> fail "can't handle unboxed single constructor" -- todo: fixme
    ; _ {- | isStar qualName -> return (TH.ConT (TH.mkName "GHC.Types.[]")) -- the XHaskell type -> Haskell type translation should be done some where else
        | isOr   qualName -> return (TH.ConT (TH.mkName "Data.Either.Either"))
        | isEps  qualName -> return (TH.TupleT 0)
        | otherwise  -} -> do   
          { qQualName <- translateQName qualName
          ; return (TH.ConT qQualName)
          }
    }
translateType (TyParen t) = translateType t
translateType (TyInfix t1 qualName t2) = do
  { qt1 <- translateType t1
  ; qt2 <- translateType t2
  ; case qualName of
    { Special UnitCon -> fail "() appears as an infix type constr"  -- nofix
    ; Special ListCon -> fail "[] appears as an infix type constr"  -- nofix
    ; Special FunCon  -> return (TH.AppT (TH.AppT TH.ArrowT qt1) qt2)
    ; Special (TupleCon Unboxed _) -> fail "can't handle unboxed tupple type" -- nofix: TH does not support
    ; Special (TupleCon Boxed i)   -> fail "(,) appears as an infix type constr"  -- nofix
    ; Special Cons                 -> fail "(:) appears as an infix type constr"  -- nofix
    ; Special UnboxedSingleCon     -> fail "can't handle unboxed single constructor" -- todo: fixme
    ; _ {- | isStar qualName -> fail "Star appears as an infix type constr"
        | isOr   qualName -> return (TH.AppT (TH.AppT (TH.ConT (TH.mkName "Data.Either.Either")) qt1) qt2)
        | isEps  qualName -> fail "Eps appears as an infix type constr"
        | otherwise -} -> do    
          { qQualName <- translateQName qualName
          ; return (TH.AppT (TH.AppT (TH.ConT qQualName) qt1) qt2)
          }
    } 
  }
translateType (TyKind t kind) = do 
  { qt <- translateType t
  ; qkind <- translateKind kind
  ; return (TH.SigT qt qkind)
  } 


-- | translate a context
translateContext :: Context -> TH.Q TH.Cxt        
translateContext = mapM translateAsst 
-- | translate an assertion to a predicate
translateAsst :: Asst -> TH.Q TH.Pred
translateAsst (ClassA qname ts) = do 
  { name <- translateQName qname
  ; qts  <- mapM translateType ts 
  ; return $ foldl (\t s -> TH.AppT t s) (TH.ConT name) qts
  }
translateAsst (InfixA t1 qname t2) = translateAsst (ClassA qname [t1,t2]) 
translateAsst (IParam _ _) = fail "unable to handle implicit params"
translateAsst (EqualP t1 t2) = do 
  { qt1 <- translateType t1
  ; qt2 <- translateType t2
  ; return (TH.AppT (TH.AppT TH.EqualityT qt1) qt2) 
  }


-- | translate the type variable binder                               
translateTyVarBind :: TyVarBind -> TH.Q TH.TyVarBndr
translateTyVarBind (KindedVar name kind) = do 
  { qname <- translateName name 
  ; qkind <- translateKind kind
  ; return (TH.KindedTV qname qkind)
  } 
translateTyVarBind (UnkindedVar name) = do                                            
  { qname <- translateName name
  ; return (TH.PlainTV qname) 
  }
                                        


-- |  translate a name from Haskell Source Exts to Template Haskell Representation
translateName :: Name -> TH.Q TH.Name
translateName (Ident name)  = return (TH.mkName name)
translateName (Symbol name) = return (TH.mkName name)

-- | reverse function of translateName -- todo
untranslateName :: TH.Name -> Name
untranslateName name = Ident (TH.nameBase name)

-- | translate a qualified name from Haskell Source Exts to Template Haskell Representation
translateQName :: QName -> TH.Q TH.Name
translateQName (Qual (ModuleName mn) (Ident n)) = return (TH.mkName (mn ++ "." ++ n))
translateQName (Qual (ModuleName mn) (Symbol n)) = return (TH.mkName (mn ++ "." ++ n))
translateQName (UnQual name) = translateName name
translateQName (Special UnitCon) = return $ TH.mkName "()"
translateQName (Special ListCon) = return $ TH.mkName "[]"
translateQName (Special specialCon) = fail $ "special contructor " ++ prettyPrint specialCon ++  " is appleid to translateQName" -- nofix: this is already handled: see translateType



-- | lookup the quanlified name's type from the XHaskell Type Environment, otherwise call reify to recover the Haskell type
lookupQName :: QName -> TyEnv -> TH.Q (TH.Type, [Name])
lookupQName (Special UnitCon) _ = do 
  { let name = TH.mkName "()"
  ; return (TH.ConT name, [])
  }
lookupQName qn tenv = 
  let n = case qn of {UnQual x-> x; Qual mn x -> x; e -> error (show e)}
  in case M.lookup n tenv of 
  { Just (t,ns)  -> do 
       { -- qt <- translateType t -- already in TH.Type
       ; t' <- T.renameVars t
       ; return (t',ns)
       }
  ; Nothing -> do  
       { qName <- translateQName qn
       ; sInfo <- TH.reify qName
       ; case sInfo of
         { TH.VarI name t mb_dec fixity -> return (t,[])
         ; TH.DataConI name t dataTyName fixity -> return (t, [])
         ; TH.ClassOpI name t tyClassName fixity -> return (t, []) 
         ; _ -> fail (show n ++ " is not a variable nor a constructor.") -- todo : the record data type constructor case
         }
       }
  }

-- | lookup the type of the given literal
checkLitTy :: Literal -> TH.Q TH.Type
checkLitTy (Char _)       = return $ TH.ConT (TH.mkName "Char") -- todo : the module name
checkLitTy (String _)     = return $ TH.ConT (TH.mkName "String")
checkLitTy (Int _)        = return $ TH.ConT (TH.mkName "Int")
checkLitTy (Frac _)       = return $ TH.ConT (TH.mkName "Rational")
checkLitTy (PrimInt _)    = return $ TH.ConT (TH.mkName "Int")
checkLitTy (PrimWord _)   = return $ TH.ConT (TH.mkName "Word")
checkLitTy (PrimFloat _)  = return $ TH.ConT (TH.mkName "Float")
checkLitTy (PrimDouble _) = return $ TH.ConT (TH.mkName "Double")
checkLitTy (PrimChar _)   = return $ TH.ConT (TH.mkName "Char")
checkLitTy (PrimString _) = return $ TH.ConT (TH.mkName "String")

