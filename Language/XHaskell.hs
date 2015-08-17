{-# LANGUAGE MultiParamTypeClasses,TemplateHaskell,QuasiQuotes #-}

module Language.XHaskell where


import Data.List (zip4,sort,nub,foldl1)
import qualified Data.Traversable as Trvsbl (mapM)
-- import Data.Generics
import Control.Monad
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import qualified Data.Map as M


import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Syntax
import Language.Haskell.Exts.Extension
import Language.Haskell.Exts.Pretty



import qualified Language.XHaskell.Source as S 
import qualified Language.XHaskell.Target as T 
import Language.XHaskell.Error
import Language.XHaskell.Subtype 
import Language.XHaskell.Environment ( TyEnv, mkTyEnv, addTyEnv, addRecTyEnv, unionTyEnv, 
                                       BdEnv, mkBdEnv,
                                       ClEnv, mkClEnv, mkClTyEnv,
                                       mkDtTyEnv,
                                       InstEnv, mkInstEnv,
                                       Constraint, ConstrEnv, unionConstrEnv, cxtToConstrs, cxtToConstrEnv, addConstrEnv, buildConstrEnv, deducible,
                                       translateKind, translateType, translateContext, translateAsst, translateTyVarBind, 
                                       translateName, translateQName, untranslateName,
                                       lookupQName, checkLitTy
                                     )

import Language.XHaskell.LocalTypeInference ( SubtypeConstr, genSubtypeConstrs, solveSubtypeConstrs, 
                                              collapseConstrs, findMinSubst
                                            )

-- | main function
xhDecls :: String -> TH.DecsQ
xhDecls s = case parseModuleWithMode S.xhPm s of 
  { ParseFailed srcLoc errMsg -> failWithSrcLoc srcLoc $ "Parser failed " ++ errMsg
  ; ParseOk (Module srcLoc moduleName pragmas mb_warning mb_export import_decs decs) -> do 
       { let tySigs    = filter S.isTypeSig decs
             funBinds  = filter S.isFunBind decs
             clDecls   = filter S.isClassDecl decs
             instDecls = filter S.isInstDecl decs 
             dtDecls   = filter S.isDtDecl decs
                   
       ; tyEnv1 <- mkTyEnv tySigs    -- the type environment is using TH.Type
       ; tyEnv2 <- mkClTyEnv clDecls
       ; tyEnv3 <- mkDtTyEnv dtDecls 
                   
       ; let tyEnv     = tyEnv1 `unionTyEnv` tyEnv2  `unionTyEnv` tyEnv3 -- 2) get the type environment
             bdEnv     = mkBdEnv funBinds                                -- 3) build the function name -> def binding environment
             clEnv     = mkClEnv clDecls                                 -- 4) get the type class environment, name -> vars, functional dep, classFuncDecs
             instEnv   = mkInstEnv instDecls                         -- we don't need this -- 5) get the type class instance decls
        
       ; decsTH <- translateDecs tyEnv bdEnv clEnv instEnv decs 
                     -- 6) for each type sig \in tyTEnv, 
                     --   a) translate the type signatures to haskell representation
                     --   b) translate the body decl to haskell representation        
       ; return decsTH }
  }

                                 

translateDataDecl :: Decl -> TH.Q TH.Dec 
translateDataDecl (DataDecl srcLoc DataType context dtName tyVarBinds qualConDecls derivings) = do 
  { cxt <- translateContext context 
  ; dtName' <- translateName dtName
  ; tyVarBinds' <- mapM translateTyVarBind tyVarBinds
  ; cons <- mapM translateQualConDecl qualConDecls
  ; names <- mapM translateDeriving derivings
  ; return $ TH.DataD cxt dtName' tyVarBinds' cons names 
  }
translateDataDecl (DataDecl srcLoc NewType context dtName tyVarBinds qualConDecls derivings) = do
  { cxt <- translateContext context 
  ; dtName' <- translateName dtName
  ; tyVarBinds' <- mapM translateTyVarBind tyVarBinds
  ; con <- translateQualConDecl (head qualConDecls)
  ; names <- mapM translateDeriving derivings
  ; return $  TH.NewtypeD cxt dtName' tyVarBinds' con names 
  }

translateQualConDecl :: QualConDecl -> TH.Q TH.Con
translateQualConDecl (QualConDecl srcLoc [] [] (ConDecl dcName dtypes)) = do
  -- NormalC
  { sTys <- mapM translateBangType dtypes 
  ; name' <- translateName dcName
  ; return (TH.NormalC name' sTys) 
  }
translateQualConDecl (QualConDecl srcLoc [] [] (RecDecl dcName names_type_pair)) = do
  -- RecC
  { varStrictTypes <- mapM (\ (names, dtype) -> do
                              { (s,ty) <- translateBangType dtype 
                              ; names' <- mapM translateName names
                              ; return (map (\name' -> (name', s, ty)) names')
                              } ) names_type_pair 
  ; name' <- translateName dcName
  ; return (TH.RecC name' (concat varStrictTypes))
  }
translateQualConDecl (QualConDecl srcLoc [] [] (InfixConDecl dtype1 dcName dtype2)) = do   
  -- InfixC
  { name' <- translateName dcName
  ; sty1  <- translateBangType dtype1
  ; sty2  <- translateBangType dtype2
  ; return (TH.InfixC sty1 name' sty2)
  }
translateQualConDecl (QualConDecl srcLoc tyVarBinds context condecl) = do 
  { con   <- translateQualConDecl (QualConDecl srcLoc [] [] condecl) 
  ; tyVarBinds' <- mapM translateTyVarBind tyVarBinds
  ; context'    <- translateContext context
  ; return (TH.ForallC tyVarBinds' context' con)
  }
  

translateBangType :: Type -> TH.Q (TH.Strict, TH.Type)
translateBangType (TyBang BangedTy t) = do
  { t' <- translateType t
  ; return (TH.IsStrict, T.xhTyToHsTy t')
  }
translateBangType (TyBang UnpackedTy t) = do
  { t' <- translateType t
  ; return (TH.Unpacked, T.xhTyToHsTy t')
  }
translateBangType t = do
  { t' <- translateType t
  ; return (TH.NotStrict, T.xhTyToHsTy t')
  }

  
  

translateDeriving :: Deriving -> TH.Q TH.Name
translateDeriving (qname, tys) = translateQName qname -- what are the types 'tys'?




-- getting across target and src types

instance Subtype TH.Type Type where 
  ucast srcLoc t1 t2 = do 
    { t2' <- translateType t2
    ; ucast srcLoc t1 t2' 
    }
  dcast srcLoc t1 t2 = do
    { t2' <- translateType t2
    ; dcast srcLoc t1 t2' 
    }



-- | translate XHaskell Decls (in Language.Haskell.Exts.Syntax ) to Template Haskell (in Language.Haskell.TH.Syntax)
translateDecs :: TyEnv -> BdEnv -> ClEnv -> InstEnv -> [Decl] -> TH.Q [TH.Dec]
translateDecs tyEnv bdEnv clEnv instEnv [] = return []
{-
tenv U { (f:t) }, bdEnv, clEnv |- bdEnv(f) : t ~> E
------------------------------------------------------------
tenv, bdEnv, clEnv |- f : t ~> f : [[t]] 
                             f = E
-}
translateDecs tyEnv bdEnv clEnv instEnv ((TypeSig src idents ty):decs) = do  
  -- The translation is triggered by the type signature (which is compulsory in xhaskell) 
  -- The function bindings are read off from bdEnv. Those remain in decs will be skipped.
  { qDecs <- mapM (\ident -> translateFunc tyEnv bdEnv clEnv instEnv ident) idents
  -- ; TH.runIO (putStrLn (TH.pprint qDecs))
  ; qDecss <- translateDecs tyEnv bdEnv clEnv instEnv decs 
  ; return ((concat qDecs) ++ qDecss)
  }
translateDecs tyEnv bdEnv clEnv instEnv (dec@(InstDecl src mb_overlap tvbs ctxt name tys instDecl):decs) = do 
  { qDec <- translateInst tyEnv clEnv instEnv  dec
  ; qDecss <- translateDecs tyEnv bdEnv clEnv instEnv decs
  ; return (qDec:qDecss)
  }
translateDecs tyEnv bdEnv clEnv instEnv (dec@(ClassDecl src ctxt name tybnd fds classDecl):decs) = do
  { qDec   <- translateClass tyEnv clEnv instEnv dec
  ; qDecss <- translateDecs tyEnv bdEnv clEnv instEnv decs
  ; return (qDec:qDecss)
  }
translateDecs tyEnv bdEnv clEnv instEnv (dec@(DataDecl src dataOrNew context dtName tyVarBinds qualConDecls derivings):decs) = do
  { qDec <- translateDataDecl dec
  ; qDecss <- translateDecs tyEnv bdEnv clEnv instEnv decs
  ; return (qDec:qDecss)
  }
translateDecs tyEnv bdEnv clEnv instEnv (pBnd@(PatBind src p {- mbTy -} rhs bdDecs):decs) = do
  { qDec <- translatePatBind tyEnv bdEnv clEnv instEnv pBnd
  ; qDecss <- translateDecs tyEnv bdEnv clEnv instEnv decs
  ; return (qDec:qDecss)
  }
translateDecs tyEnv bdEnv clEnv instEnv (_:decs) = translateDecs tyEnv bdEnv clEnv instEnv decs                                                       


translatePatBind :: TyEnv -> BdEnv -> ClEnv -> InstEnv -> Decl -> TH.Q TH.Dec {- removed after HSX 1.16. Question when do we get this on the declaration level???
translatePatBind tyEnv bdEnv clEnv instEnv (PatBind src (PVar ident) (Just ty) (UnGuardedRhs e) bdDecs) = do 
  { let cenv = buildConstrEnv clEnv instEnv 
  ; ident' <- translateName ident
  ; ty'    <- translateType ty
  ; e'     <- translateExpC src tyEnv cenv e ty'
  ; return $ TH.ValD (TH.VarP ident') (TH.NormalB e') []
  }
-}
translatePatBind tyEnv bdEnv clEnv instEnv (PatBind src (PVar ident) {- Nothing -} (UnGuardedRhs e) bdDecs) = do 
  { let cenv = buildConstrEnv clEnv instEnv 
  ; ident' <- translateName ident
  ; case M.lookup ident tyEnv of
    { Nothing -> failWithSrcLoc src $ "unable to find type info for variable " ++ TH.pprint ident'
    ; Just (ty',_) -> do 
      { e'     <- translateExpC src tyEnv cenv e ty'
      ; return $ TH.ValD (TH.VarP ident') (TH.NormalB e') []
      }
    }
  }
  


{-
tenv, bdEnv, clEnv |- class ctxt => C \bar{t} | \bar{fd} where \bar{f:t'} ~> 
    class ctxt => C \bar{t} | \bar{fd} where \bar{f:[[t']]}
-}
translateClass :: TyEnv -> ClEnv -> InstEnv -> Decl -> TH.Q TH.Dec
translateClass tyEnv clEnv instEnv (ClassDecl src ctxt name tybnds fds classDecls) = do
  { ctxt' <- translateContext ctxt
  ; name' <- translateName name 
  ; tybnds' <- mapM translateTyVarBind tybnds
  ; fds'    <- mapM translateFunDep fds
  ; classDecls' <- mapM translateClassDecl classDecls
  ; return (TH.ClassD ctxt' name' tybnds' fds' (concat classDecls'))
  }
  
                                                                 
{-                                                             
clEnv(C) = class C \bar{a} | \bar{fd} where \bar{f:t'} 
theta = [\bar{t/a}]
tenv_c = \bar{f:theta(t')}
tenv U tenv_c, bdEnv, clEnv U \theta(ctxt) |- \bar{f = e : \theta(t')} ~> \bar{f = E}
-------------------------------------------------------------------------------------------------                          
tenv, bdEnv, clEnv |- instance ctxt => C \bar{t} where \bar{f=e} ~> instance ctxt => C \bar{[[t]]} where \bar{f=E}
-}             
translateInst :: TyEnv -> ClEnv -> InstEnv -> Decl -> TH.Q TH.Dec
translateInst tyEnv clEnv instEnv (InstDecl src mb_overlap tvbs ctxt (UnQual name) tys instDecls) = do 
  { ctxt'  <- translateContext ctxt
  ; name' <- translateName name
  ; tys'   <- mapM translateType tys
    -- look for the theta, and the type class function definitions \bar{ f : t'} 
  ; mbSubsts <- case M.lookup name clEnv of 
    { Nothing -> {- get from reification -} 
         do { info <- TH.reify name' 
            ; case info of
              { TH.ClassI (TH.ClassD cxt name tvbs fds decs) classInstances -> do 
                   -- subst from TH.names to TH.types
                   -- tyEnv from class function name to TH.type
                   -- for tyEnv, we need to convert TH.name back to name, 
                   -- todo: in future maybe tyenv should map TH.name to TH.type instead of name ot TH.type
                   { let vs = map T.getTvFromTvb tvbs
                         subst = M.fromList (zip vs tys') 
                         extractNameType (TH.SigD n t) = (untranslateName n,t)
                         tyEnv' = M.fromList (map extractNameType decs)
                   ; return (Just (subst, M.map (T.applySubst subst) tyEnv'))
                   }
              ; _ -> return Nothing
              }
            }
    ; Just (srcLoc, ctxt, tvbs, fds, classDecls) -> 
        let varNames = map (\tyVar -> case tyVar of 
                               { UnkindedVar n -> n 
                               ; KindedVar n _ -> n
                               }) tvbs
            
        in do 
          { tyEnv' <- do { ntys <- mapM (\(ClsDecl (TypeSig src idents ty)) -> do 
                                            { ty' <- translateType ty
                                            ; return (zip idents (repeat ty'))
                                            }) classDecls
                         ; return (M.fromList (concat ntys))
                         }
          ; varNames' <- mapM translateName varNames
          ; let subst = M.fromList (zip varNames' tys')                    
          ; return (Just (subst, M.map (T.applySubst subst) tyEnv'))
          }
    }
  ; case mbSubsts of 
    { Nothing -> failWithSrcLoc src $ "unable to find the class definition given the instance definition"
    ; Just (subst, tenv') -> do
      { let tenv'' = M.map (\t -> (t,[])) tenv' -- padding with the empty list of record label names
            tyEnv' = tyEnv `unionTyEnv` tenv'' 
            cenv   = buildConstrEnv clEnv instEnv 
            cenv'  = cxtToConstrEnv ctxt' 
            cenv'' = cenv `unionConstrEnv` cenv'
      ; instDecls' <- mapM (translateInstDecl tyEnv' cenv'' subst  tenv'') instDecls 
      ; let htys' = map T.xhTyToHsTy tys'
      ; let ty' = foldl TH.AppT (TH.ConT name') htys'
      ; return (TH.InstanceD ctxt' ty' instDecls')
      }
    }
  }
translateInst tyEnv clEnv instEnv (InstDecl src mb_overlap tvbs ctxt qname@(Qual modName name) tys instDecls) = -- since the the modName is qualified, it must be from another module 
  do 
    { ctxt'  <- translateContext ctxt
    ; name' <- translateQName qname
    ; tys'  <- mapM translateType tys
    ; mbSubsts <- do
      { info <- TH.reify name' 
      ; case info of
        { TH.ClassI (TH.ClassD cxt name tvbs fds decs) classInstances -> do 
             -- subst from TH.names to TH.types
             -- tyEnv from class function name to TH.type
             -- for tyEnv, we need to convert TH.name back to name, 
             -- todo: in future maybe tyenv should map TH.name to TH.type instead of name ot TH.type
             { let vs = map T.getTvFromTvb tvbs
                   subst = M.fromList (zip vs tys') 
                   extractNameType (TH.SigD n t) = (untranslateName n,t)
                   tyEnv' = M.fromList (map extractNameType decs)
             ; return (Just (subst, M.map (T.applySubst subst) tyEnv'))
             }
        ; _ -> return Nothing
        }
      } 
  ; case mbSubsts of 
    { Nothing -> failWithSrcLoc src $ "unable to find the class definition given the instance definition"
    ; Just (subst, tenv') -> do
      { let tenv'' = M.map (\t -> (t,[])) tenv' -- padding with the empty list of record label names
            tyEnv' = tyEnv `unionTyEnv` tenv''
            cenv   = buildConstrEnv clEnv instEnv 
            cenv'  = cxtToConstrEnv ctxt' 
            cenv'' = cenv `unionConstrEnv` cenv'
      ; instDecls' <- mapM (translateInstDecl tyEnv' cenv'' subst tenv'') instDecls 
      ; let ty' = foldl TH.AppT (TH.ConT name') tys'
      ; return (TH.InstanceD ctxt' ty' instDecls')
      }
    }
  }

-- | translate the instance function declaration
translateInstDecl ::  TyEnv -> ConstrEnv -> T.Subst -> TyEnv -> InstDecl -> TH.Q TH.Dec
translateInstDecl tyEnv cenv subst tyEnv' (InsDecl (FunBind matches@((Match srcLoc name _ _ _ _):_))) = 
  case M.lookup name tyEnv' of
    { Nothing -> failWithSrcLoc srcLoc $ "unable to find type info for instance method"
    ; Just (ty,_) -> translateBody srcLoc tyEnv cenv name ty matches 
    }
  -- translateBody tyEnv clEnv instEnv name ty matches
translateInstDecl _ _ _ _ _ = fail "associate data type declaration in type class instance is not suppported."
  

-- | translate a function definition                                                       
translateFunc :: TyEnv -> BdEnv -> ClEnv -> InstEnv -> Name -> TH.Q [TH.Dec]
translateFunc tyEnv bdEnv clEnv instEnv name =
  case (M.lookup name tyEnv, M.lookup name bdEnv) of
    { (Just (ty,_), Just matches@((Match srcLoc _ _ _ _ _):_)) -> do 
         { qTySig   <- translateTypeSig name ty 
         ; let cenv = buildConstrEnv clEnv instEnv
         ; qFunDec  <- translateBody srcLoc tyEnv cenv name ty matches
         ; return [qTySig, qFunDec]
         }
    ; (_, _)                  -> return [] 
    }
  
{- not needed
isPolymorphic :: Type -> Bool  
isPolymorphic (TyForall _  ctxt t) = isPolymorphic t
isPolymorphic (TyFun t1 t2) = isPolymorphic t1 || isPolymorphic t2
isPolymorphic (TyTuple _ ts) = any isPolymorphic ts
isPolymorphic (TyList t) = isPolymorphic t
isPolymorphic (TyApp t1 t2) = isPolymorphic t1 || isPolymorphic t2
isPolymorphic (TyVar _ ) = True
isPolymorphic (TyCon _ ) = False
isPolymorphic (TyParen t) = isPolymorphic t
isPolymorphic (TyInfix t1 qop t2) = isPolymorphic t1 || isPolymorphic t2
isPolymorphic (TyKind t k) = False
-}

  
                                                  
-- | translate a type signature, the XHaskell type will be turned into Haskell type
translateTypeSig :: Name -> TH.Type -> TH.Q TH.Dec                                                      
translateTypeSig name ty = do 
  { qName <- translateName name
  -- ; qType <- translateType ty -- already in TH.Type
  ; let hsType = T.xhTyToHsTy ty
  ; return (TH.SigD qName hsType) 
  {-     tvs = nub (sort (T.typeVars hsType))
  ; if (length tvs == 0) 
    then return (TH.SigD qName hsType) 
    else return (TH.SigD qName (TH.ForallT (map (\n -> TH.PlainTV n) tvs) emptyCtxt hsType)) 
  -}
  }
  where emptyCtxt = []
                           
                               

-- | translate the functional dependency
translateFunDep :: FunDep -> TH.Q TH.FunDep
translateFunDep (FunDep names names') = do
  { names'' <- mapM translateName names
  ; names''' <- mapM translateName names' 
  ; return (TH.FunDep names'' names''')
  }
  

-- | translate the class function declaration
translateClassDecl :: ClassDecl -> TH.Q [TH.Dec]
translateClassDecl (ClsDecl (TypeSig src idents ty)) = do 
  { ty' <- translateType ty 
  ; mapM (\ident -> translateTypeSig ident ty') idents
  }
translateClassDecl (ClsDecl decl) | S.isFunBind decl = fail "default function declaration in type class is not supported." 
translateClassDecl (ClsDataFam _ _ _ _ _) = fail "associate data type declaration in type class is not suppported."
translateClassDecl (ClsTyFam _ _ _ _) = fail "type family declaration in type class is not suppported."
translateClassDecl (ClsTyDef _ _ _) =  fail "associate type synonum declaration in type class is not suppported."

                                        
                                        




-- | translate a literal from Haskell Source Exts to Template Haskell Representation
translateLit :: Literal -> TH.Q TH.Lit
translateLit (Char c)   = return (TH.CharL c)
translateLit (String s) = return (TH.StringL s)
translateLit (Int i)    = return (TH.IntegerL i)
translateLit (Frac r)   = return (TH.RationalL r)
translateLit (PrimInt i) = return (TH.IntPrimL i)
translateLit (PrimWord w) = return (TH.WordPrimL w)
translateLit (PrimFloat f) = return (TH.FloatPrimL f)
translateLit (PrimDouble d) = return (TH.DoublePrimL d)
translateLit (PrimChar c) = return (TH.CharL c)
translateLit (PrimString s) = return (TH.StringL s)



-- | translate the body of a function definition, which is a list of match-clauses from Haskell Source Exts to Template Haskell Representation
translateBody :: SrcLoc -> TyEnv -> ConstrEnv -> Name -> TH.Type -> [Match] -> TH.Q TH.Dec
translateBody pSrcLoc tenv cenv name ty ms = do 
  { e  <- desugarMatches pSrcLoc ms 
  ; qe <- translateExpC pSrcLoc tenv cenv e ty 
  ; qName <- translateName name
  ; return (TH.ValD (TH.VarP qName) (TH.NormalB qe) [{-todo:where clause-}] ) -- f = \x -> ...
  } 
                                
{- | desugaring the function pattern syntax to the unabridged version
 f [p = e] ==> f = \x -> case x of [p -> e]
-}
                                
desugarMatches pSrcLoc ms = do 
  { alts <- mapM matchToAlt ms
  ; let srcLoc = pSrcLoc
        e    =  Lambda srcLoc [PVar (Ident "x")] (Case (Var (UnQual (Ident "x"))) alts)
  ; return e
  }
  where matchToAlt (Match srcLoc name [p] mbTy rhs binds) =
         return (Alt srcLoc p rhs binds)
  {-
  where matchToAlt (Match srcLoc name [p] mbTy rhs binds) = do
          { let guardAlt = rhsToGuardAlt rhs
          ; return (Alt srcLoc p guardAlt binds) }
        matchToAlt (Match srcLoc name _ mbTy rhs binds) = failWithSrcLoc srcLoc $ "can't handle multiple patterns binding \"f p1 p2 ... = e\" yet"
        rhsToGuardAlt (UnGuardedRhs e) = UnGuardedAlt e
        rhsToGuardAlt (GuardedRhss grhss) = GuardedAlts (map gRhsToGAlt grhss)
        gRhsToGAlt (GuardedRhs srcLoc stmts e) = GuardedAlt srcLoc stmts e
        -}    

{-
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|   tenv |- e : t ~> E     |
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-}

{-
getType :: String -> TH.Q TH.Info              
getType s = do
  { let n = TH.mkName s
  ; info <- TH.reify n
  ; return info -- we will get can't run reify in IO Monad error if we do it in GHCi, we need
    -- $(TH.stringE . show =<< TH.reify (TH.mkName "map"))
  }
-}




{-
*XHaskell Data.Typeable Language.Haskell.Exts.Pretty Language.Haskell.TH.Ppr> let (ParseOk t) = parseType ("Choice (Star Char) Int")
*XHaskell Data.Typeable Language.Haskell.Exts.Pretty Language.Haskell.TH.Ppr> x <- TH.runQ $ translateType t
*XHaskell Data.Typeable Language.Haskell.Exts.Pretty Language.Haskell.TH.Ppr> toRE x
Choice (Star (L "Char")) (L "Int")
-}



-- | translation of expression from Haskell Source Exts to TH. 
-- | semantic subtyping is translated into ucast and regular expression pattern matching is translated into dcast
-- | type checking mode



translateExpC :: SrcLoc -> TyEnv -> ConstrEnv -> Exp -> TH.Type -> (TH.Q TH.Exp)
translateExpC pSrcLoc tenv cenv e@(Var qn) ty = do 
  { (ty',_)   <- lookupQName qn tenv  
  ; case (T.isMono ty, T.isMono ty') of 
{-
   x : t' \in tenv
   |-  t' <= t ~> u 
  --------------------- (CVarM)
   tenv, cenv |-^c x : t ~> u x

-}    
    { (True, True) -> -- both are mono types
         do 
           { uc    <- ucast pSrcLoc ty' ty
           ; qName <- translateQName qn
           ; return (TH.AppE uc (TH.VarE qName))
           }
{-
   x : \forall \bar{a}. C' => t' \in tenv
   C' == C    t' == t    note: == modulo \bar{a}
  --------------------- (CVarP)
   tenv, cenv |-^c x : \forall \bar{a}. C => t ~> x
-}
    ; (False, False) | T.isomorphic ty ty' -> do
           { qName <- translateQName qn
           ; return (TH.VarE qName)
           } 
 {- The inferred type is poly, but the incoming type is mono, it is a type application                                              
   x : \forall \bar{a}. C' => t' \in tenv
   dom(theta) = \bar{a}
   theta(t') = t     note theta is a just substitution that grounds t' to t
   theta(C) \subseteq cenv 
  --------------------- (CVarA)
   tenv, cenv |-^c x : t ~> u x
-}
    ; (True, False) -> 
           case ty' of 
             { TH.ForallT tvbs cxt ty'' -> 
               case T.findSubst ty' ty of
                 { Just theta -> do
                      { let constrs = cxtToConstrs $ T.applySubst theta cxt
                      ; qName <- translateQName qn
                      ; if (deducible constrs cenv)
                         then return (TH.VarE qName)
                         else failWithSrcLoc pSrcLoc $ "Unable to deduce " ++ (TH.pprint cxt) ++ " from the context " ++ (show cenv)
                      }
                 ; Nothing    -> failWithSrcLoc pSrcLoc $ "Unable to build substitution of " ++ (prettyPrint e)  ++ ":" ++ (TH.pprint ty') ++ " from the type " ++ (TH.pprint ty)
                 }
             }
    ; _ -> failWithSrcLoc pSrcLoc $ "translation failed. Trying to match expected type " ++ (TH.pprint ty)  ++ " with inferred type " ++ (TH.pprint ty')
    }
  }  
translateExpC pSrcLoc tenv cenv e@(Con qn) ty = do 
  { (ty',_)   <- lookupQName qn tenv  
  ; case (T.isMono ty, T.isMono ty') of 
{-
   K : \forall a. C' => t' \in tenv
   C' == C    t' == t
  --------------------- (CConP)
   tenv, cenv |-^c K : \forall a. C => t ~> x
-}
    { (True, True) -> -- both are mono types
         do 
           { uc    <- ucast pSrcLoc ty' ty             
           ; qName <- translateQName qn
           ; return (TH.AppE uc (TH.ConE qName))
           }
{-
   K : t' \in tenv
   |-  t' <= t ~> u 
  --------------------- (CConM)
   tenv, cenv |-^c K : t ~> u x
-}
    ; (False, False) | T.isomorphic ty ty' -> do 
           { qName <- translateQName qn
           ; return (TH.ConE qName) 
           }
{-                                              
   K : \forall \bar{a}. C' => t' \in tenv
   dom(theta) = \bar{a}
   theta(t') = t     note theta is a just subsitution that grounds t' to t
   theta(C) \subseteq cenv 
  --------------------- (CConA)
   tenv, cenv |-^c K : t ~> x
-}                                              
    ; (True, False) -> 
           case ty' of 
             { TH.ForallT tvbs cxt ty'' -> 
               case T.findSubst ty' ty of
                 { Just theta -> do
                      { let constrs = cxtToConstrs $ T.applySubst theta cxt
                      ; qName <- translateQName qn
                      ; if (deducible constrs cenv)
                         then return (TH.ConE qName)
                         else failWithSrcLoc pSrcLoc $ "Unable to deduce " ++ (TH.pprint cxt) ++ " from the context " ++ (show cenv)
                      }
                 ; Nothing    -> failWithSrcLoc pSrcLoc $ "Unable to build substitution of " ++ (prettyPrint e)  ++ ":" ++ (TH.pprint ty') ++ " from the type " ++ (TH.pprint ty)
                 }
             }
           
    ; _ -> failWithSrcLoc pSrcLoc $ "translation failed. Trying to match expected type " ++ (TH.pprint ty)  ++ " with  inferred type " ++ (TH.pprint ty')
    }
  }
{-
  |- Lit : t' 
  t' <= t ~> u
  --------------------------- (CLit)
  tenv, cenv |-^c Lit : t ~> u Lit
-}
translateExpC pSrcLoc tenv cenv (Lit l) ty = do
  { ql  <- translateLit l
  ; ty' <- checkLitTy l
  ; uc  <- ucast pSrcLoc ty' ty             
  ; return (TH.AppE uc (TH.LitE ql))
  }
{-                              
  (op : t1 -> t2 -> t3) \in tenv
  tenv, cenv |-^i e1 : t1' ~> E1
  tenv, cenv |-^i e2 : t2' ~> E2
  |- t1' <= t1 ~> u1
  |- t2' <= t2 ~> u2
  |- t3  <= t ~> u3
 -------------------------------------- (CBinOp)
  tenv, cenv |-^c e1 `op` e2 : t ~> u3 ((op (u1 E1)) (u2 E2)) 
-} 
translateExpC pSrcLoc tenv cenv (InfixApp e1 qop e2) ty = do
  { (e1',t1') <- translateExpI pSrcLoc tenv cenv e1 
  ; (e2',t2') <- translateExpI pSrcLoc  tenv cenv e2
  ; (qn, op') <- case qop of
          { QVarOp qn -> do 
               { n <- translateQName qn 
               ; return (qn, TH.VarE n)
               }
          ; QConOp qn -> do 
               { n <- translateQName qn
               ; return (qn, TH.ConE n)
               }
          }
  ; (ty',_) <- lookupQName qn tenv -- TH type
  ; case ty' of
    { TH.AppT (TH.AppT TH.ArrowT t1) (TH.AppT (TH.AppT TH.ArrowT t2) t3) -> do
         { u1 <- ucast pSrcLoc t1' t1 
         ; u2 <- ucast pSrcLoc t2' t2
         ; u3 <- ucast pSrcLoc t3 ty 
         ; return (TH.AppE u3 (TH.AppE (TH.AppE op' (TH.AppE u1 e1')) (TH.AppE u2 e2')))
         }
    ; TH.ForallT tyVarBnds cxt t -> failWithSrcLoc pSrcLoc ((prettyPrint qop) ++ " has the the type " ++ (TH.pprint ty') ++ " is still polymorphic, please give it a type annotation.")
    ; _ -> failWithSrcLoc pSrcLoc ((prettyPrint qop) ++ ":" ++ (TH.pprint ty') ++ " is not a binary op.")
    }
  }
                                                  
{-                                                
  f : forall \bar{a}. c => t1' -> ... tn' -> r  \in tenv
   tenv,cenv |-^i ei : ti ~> Ei
   \bar{a} |- ti <: ti' ==> Di
   S = solve(D1++ ... ++Dn, r)
   |- ti <= S(ti') ~> ui
   S(c) \subseteq cenv
   S(r) <= t ~> u
  ----------------------------------------- (CEAppInf)
   tenv,cenv |-^c f e1 ... en : t ~>
      u (f (u1 E1) ... (un En))
-}
translateExpC pSrcLoc tenv cenv e@(App e1 e2) ty = do 
  { mb <- appWithPolyFunc tenv e 
  ; case mb of
      { Just (f, es) -> do 
           { (f', tyF) <- translateExpI pSrcLoc tenv cenv f
           ; e't's <- mapM (translateExpI pSrcLoc tenv cenv) es
           ; case tyF of
             { TH.ForallT tyVarBnds ctxt t -> do
                  { let as  = map T.getTvFromTvb tyVarBnds
                        (ts, r) = T.breakFuncType t (length e't's)
                        es' = map fst e't's
                        ts' = map snd e't's
                        ds  = concatMap (\(t,t') -> genSubtypeConstrs as [] t t') (zip ts' ts)
                  ; s <- solveSubtypeConstrs ds r
                  {- ; TH.runIO ((putStrLn "====") >> putStrLn (prettyPrint e) >> (putStrLn ("s" ++ (show s))))
                  ; TH.runIO (putStrLn ("ts':" ++ (TH.pprint ts')))
                  ; TH.runIO (putStrLn ("t:" ++ (TH.pprint t)))
                  ; TH.runIO (putStrLn ("ds:" ++ (show ds)))
                  ; TH.runIO (putStrLn ("r:" ++ (TH.pprint r))) -}
                  ; if deducible (cxtToConstrs $ T.applySubst s ctxt) cenv
                    then do 
                      { -- TH.runIO (putStrLn (TH.pprint (T.applySubst s t)))
                      ; us <- mapM (\(t,t') -> inferThenUpCast pSrcLoc t t' -- t might be still polymorphic                               
                                   ) (zip ts' (map (T.applySubst s) ts))

                      ; let ues = map (\(u,e) -> TH.AppE u e) (zip us es')
                      ; u <- ucast pSrcLoc (T.applySubst s r) ty
                      ; return (TH.AppE u (foldl TH.AppE f' ues))
                      }
                    else failWithSrcLoc pSrcLoc $ "Unable to deduce " ++ (TH.pprint (T.applySubst s ctxt)) ++ "from the context " ++ show cenv 
                  }
             ; _ -> failWithSrcLoc pSrcLoc (TH.pprint tyF ++ " is not polymorphic.")
             }
           }
      ; _ -> do 
                                                  
{-                                               
   tenv, cenv |-^I e1 : t1 -> t2 ~> E1 
   tenv, cenv |-^I e2 : t1' ~> E2
   |- t1' <= t1 ~> u1
   |- t2 <= t  ~> u2
  ------------------------------------- (CEApp)
    tenv , cenv |-^c e1 e2 : t ~> u2 (E1 (u1 E2))
-}
  
           { (e1', t12) <- translateExpI pSrcLoc tenv cenv e1
           ; case t12 of
             { TH.AppT (TH.AppT TH.ArrowT t1) t2 -> do 
                  { (e2', t1') <- translateExpI pSrcLoc tenv cenv e2
                  ; u1 <- ucast pSrcLoc t1' t1
                  ; u2 <- ucast pSrcLoc t2  ty
                  ; return (TH.AppE u2 (TH.AppE e1' (TH.AppE u1 e2')))
                  }
             ; TH.ForallT tyVarBnds cxt t -> failWithSrcLoc pSrcLoc ((prettyPrint e1) ++ ":" ++ (TH.pprint t12) ++ " is still polymorphic, please give it a type annotation.")  
             ; _ -> failWithSrcLoc pSrcLoc ((prettyPrint e1) ++ ":" ++ (TH.pprint t12) ++ " is not a function.")
             }
           }
      }
  }
{-                                    
  tenv, cenv |-^c e : t ~> E
----------------------------- (CNeg)
  tenv, cenv |-^c -e : t ~> -E
-}
translateExpC pSrcLoc tenv cenv (NegApp e) ty = do
  { e' <- translateExpC pSrcLoc tenv cenv e ty
  ; return (TH.AppE (TH.VarE (TH.mkName "GHC.Num.negate")) e')
  }
{-
 tenv U {(x:t1)}, cenv U C |- e : t2 ~> E
 --------------------------------------------------------------------(CAbs)
 tenv, cenv |-^c \x -> e : \forall \bar{a} C => t1 -> t2 ~> \x -> E
-}
translateExpC pSrcLoc tenv cenv e1@(Lambda srcLoc [PVar x] e) ty = 
  case ty of 
    { TH.AppT (TH.AppT TH.ArrowT t1) t2 -> do
         { let tenv' = addTyEnv x t1 tenv
         ; e' <- translateExpC srcLoc tenv' cenv e t2 
         ; x' <- translateName x
         ; return (TH.LamE [TH.VarP x'] e')
         }
    ; TH.ForallT tvbs ctxt (TH.AppT (TH.AppT TH.ArrowT t1) t2) -> do 
         { let tenv' = addTyEnv x t1 tenv
               cenv' = addConstrEnv ctxt cenv
         ; e' <- translateExpC srcLoc tenv' cenv' e t2
         ; x' <- translateName x
         ; return (TH.LamE [TH.VarP x'] e')
         }
    ; _ -> failWithSrcLoc srcLoc $ ((prettyPrint e1) ++ ":" ++ (TH.pprint ty) ++ " is not a function.")
    }
{-
   tenv U {(x:t3)}, cenv |- e : t2 ~> E
   t1 <=  t3  ~> u
   -------------------------------------------------------(CAbsVA)
   tenv, cenv |-^c \x:t3 -> e :  t1 -> t2 ~> (\x -> E) . u
-}
translateExpC pSrcLoc tenv cenv e1@(Lambda srcLoc [(PParen (PatTypeSig srcLoc' (PVar x) t3))] e) ty = 
  case ty of 
    { TH.AppT (TH.AppT TH.ArrowT t1) t2 -> do
         { t3' <- translateType t3
         ; u <- ucast srcLoc' t1 t3'
         ; let tenv' = addTyEnv x t3' tenv
         ; e' <- translateExpC srcLoc tenv' cenv e t2 
         ; x' <- translateName x
         ; y  <- TH.newName "y"
         ; return (TH.LamE [TH.VarP y] (TH.AppE (TH.LamE [TH.VarP x'] e') (TH.AppE u (TH.VarE y))))
         }
    ; TH.ForallT tvbs ctxt (TH.AppT (TH.AppT TH.ArrowT t1) t2) -> 
         failWithSrcLoc srcLoc $ ((prettyPrint e1) ++ " has an polymorphic type annotation " ++ (TH.pprint ty))
    ; _ -> failWithSrcLoc srcLoc $ ((prettyPrint e1) ++ ":" ++ (TH.pprint ty) ++ " is not a function.")
    }
{-
 tenv, cenv |-^c \x -> case x of p -> e : t1 -> t2 ~> E
---------------------------------------------
 tenv, cenv |-^c \p -> e : t1 -> t2 ~> \x -> E
-}
translateExpC pSrcLoc tenv cenv e0@(Lambda srcLoc [p] e) ty = 
  translateExpC pSrcLoc tenv cenv (Lambda srcLoc [PVar (Ident "x")]
                                   (Case (Var (UnQual (Ident "x"))) [Alt srcLoc p (UnGuardedRhs e) (BDecls [])])) ty 



translateExpC pSrcLoc tenv cenv (Lambda srcLoc ps e) ty = failWithSrcLoc srcLoc $  "can't handle multiple patterns lambda yet."

translateExpC pSrcLoc tenv cenv (Let binds e) ty = failWithSrcLoc pSrcLoc $ "can't handle let bindings yet."

{- tenv |-^c e1 : Bool ~> E1
   tenv |-^c e2 : t ~> E2
   tenv |-^c e3 : t ~> E3
------------------------------------------------------------ (CIf)
tenv |-^c if e1 then e2 else e3 : t ~> if E1 then E2 else E3
-}
translateExpC pSrcLoc tenv cenv (If e1 e2 e3) ty = do 
  { e1' <- translateExpC pSrcLoc tenv cenv e1 (TH.ConT (TH.mkName "Bool")) 
  ; e2' <- translateExpC pSrcLoc tenv cenv e2 ty
  ; e3' <- translateExpC pSrcLoc tenv cenv e3 ty
  ; return (TH.CondE e1' e2' e3')
  }
                                           
{- old                                       
tenv |-^I e : t ~> E'
foreach i  
    stripT p_i = t_i 
    stripP p_i = p_i'
    p_i |- tenv_i 
    tenv U tenv_i |-^c e_i : t ~> E_i
    |- t_i <= t ~> d_i
    g_i next = case d_i E of {Just p_i' -> E_i; _ -> next}
--------------------------------------------------- (CCase)
tenv |-^c case e of [p -> e] : t ~> 
   g_1 (g_2 ... (g_n (error "unexhaustive pattern")))
-}
{-
translateExpC tenv cenv (Case e alts) ty = do 
  { pis  <- mapM pat alts
  ; eis  <- mapM rhs alts
  ; pi's <- mapM patStripP pis
  ; tis  <- mapM (patStripT tenv) pis
  ; tenvis <- mapM patTEnv pis 
  ; (e', t) <- translateExpI tenv cenv e  
  ; dis  <- mapM (\ti -> dcast ti t) tis
  ; gis  <- mapM (\(di,pi',ei, tenvi) -> do 
                     { let tenv' = unionTyEnv tenvi tenv
                     ; ei' <- translateExpC tenv' cenv ei ty
                     ; return (TH.LamE [TH.VarP (TH.mkName "next")] 
                               (TH.CaseE (TH.AppE di e') 
                                [ (TH.Match (TH.ConP (TH.mkName "Just") [pi']) (TH.NormalB ei') [])
                                , (TH.Match TH.WildP (TH.NormalB (TH.VarE (TH.mkName "next"))) [] )
                                ])) 
                     }) (zip4 dis pi's eis tenvis)
  ; err <- [|error "Pattern is not exhaustive."|]
  ; return $ foldl (\e g -> TH.AppE g e) err (reverse gis)
  }
  where pat :: Alt -> TH.Q Pat
        pat (Alt srcLoc p _ _) = return p
        
        rhs :: Alt -> TH.Q Exp
        rhs (Alt srcLoc p (UnGuardedAlt e) _) = return e
        rhs _ = fail "can't handled guarded pattern."
-}
{- newly extended with nested pattern matching
 tenv,cenv |-^I e : t ~> E'
  foreach i  
    stripT p_i = t_i 
    stripP p_i = p_i'
    t_i, p_i |- tenv_i, guard_i, extract_i , p_i'', t_i'    -- new extension
    tenv U tenv_i, cenv |-^c e_i : t ~> E_i
    |- t_i <= t ~> d_i
    g_i guard_i extract_i next = case d_i E of {Just x@p_i' | guard_i x -> let p_i'' = extract_i x
     in  E_i; _ -> next}
  --------------------------------------------------- (CCaseNested)
  tenv,cenv |-^c case e of [p -> e] : t ~> 
      g_1 guard_1 extract_1 (g_2 ... (g_n guard_n extract_n (error "unexhaustive pattern")))
-}
translateExpC pSrcLoc tenv cenv (Case e alts) ty = do 
  { pis  <- mapM pat alts
  ; eis  <- mapM rhs alts
  ; pi's <- mapM (patStripP pSrcLoc) pis
  ; tis  <- mapM (patStripT pSrcLoc tenv) pis
  ; tenv_gd_ex_pi''s <- mapM (\(ti,pi) -> patEnv pSrcLoc tenv ti pi) (zip tis pis)
  ; (e', t) <- translateExpI pSrcLoc tenv cenv e  
  ; dis  <- mapM (\ti -> dcast pSrcLoc ti t) tis
  ; gis  <- mapM (\(di,pi',ei, (tenvi,gdi,exti,pi'')) -> do 
                     { let tenv' = unionTyEnv tenvi tenv
                     ; ei' <- translateExpC pSrcLoc tenv' cenv ei ty
                     ; nn  <- TH.newName "x"
                     ; return (TH.LamE [TH.VarP (TH.mkName "next")] 
                               (TH.CaseE (TH.AppE di e') 
                                [ (TH.Match (TH.ConP (TH.mkName "Just") [TH.AsP nn pi']) (TH.GuardedB [ (TH.NormalG (TH.AppE gdi (TH.VarE nn)), 
                                                                                               {- ei' -} TH.LetE [TH.ValD pi'' (TH.NormalB (TH.AppE exti (TH.VarE nn))) []] ei')]) [])
                                , (TH.Match TH.WildP (TH.NormalB (TH.VarE (TH.mkName "next"))) [] )
                                ])) 
                     }) (zip4 dis pi's eis tenv_gd_ex_pi''s)
  ; err <- [|error "Pattern is not exhaustive."|]
  ; return $ foldl (\e g -> TH.AppE g e) err (reverse gis)
  }
  where pat :: Alt -> TH.Q Pat
        pat (Alt srcLoc p _ _) = return p
        
        rhs :: Alt -> TH.Q Exp
        rhs (Alt srcLoc p (UnGuardedRhs e) _) = return e
        rhs (Alt srcLoc p _ _)  = failWithSrcLoc srcLoc $ "can't handled guarded pattern."
        
        patToExp :: TH.Pat -> TH.Exp
        patToExp (TH.VarP n)  = TH.VarE n
        patToExp (TH.ConP n ps)  = foldl (\e1 e2 -> TH.AppE e1 e2) (TH.ConE n) (map patToExp ps)
        patToExp (TH.TupP ps) = TH.TupE (map patToExp ps)
        patToExp p = error $ "patToExp failed: unexpected pattern " ++ (TH.pprint p)

{-         
tenv, cenv |-^i e1 : t1 ~> E1
tenv, cenv |-^i e2 : t2 ~> E2 
(t1,t2) <= t ~> u
--------------------------------------
tenv, cenv |-^c (e1,e2) : t ~> u (E1,E2)
-}
translateExpC pSrcLoc tenv cenv (Tuple boxed []) _ = failWithSrcLoc pSrcLoc ("empty tuple expxpression")
translateExpC pSrcLoc tenv cenv (Tuple boxed [e]) _ = failWithSrcLoc pSrcLoc ("singleton tuple expression")
translateExpC pSrcLoc tenv cenv (Tuple boxed [e1,e2]) t = do 
  { (e1',t1') <- translateExpI pSrcLoc tenv cenv e1 -- todo: ensure t, t1' and t2' are monotype
  ; (e2',t2') <- translateExpI pSrcLoc tenv cenv e2
  ; u <- ucast pSrcLoc (TH.AppT (TH.AppT (TH.TupleT 2) t1') t2') t
  ; return (TH.AppE u (TH.TupE [e1',e2']))
  }
translateExpC pSrcLoc tenv cenv (Tuple boxed (e:es)) t = do    
  { (e1',t1') <- translateExpI pSrcLoc tenv cenv e
  ; (e2',t2') <- translateExpI pSrcLoc tenv cenv (Tuple boxed es)
  ; u <- ucast pSrcLoc (TH.AppT (TH.AppT (TH.TupleT 2) t1') t2') t
  ; return (TH.AppE u (TH.TupE [e1',e2']))
  }
                                                 
{-                                                 
   tenv, cenv |-^c e : t ~> E
   t <= t' ~> u
  ------------------------------------- (CTApp)
    tenv , cenv |-^c (e :: t) : t' ~> u E
-}
translateExpC pSrcLoc tenv cenv e1@(ExpTypeSig srcLoc e t) t' = do 
  { t'' <- translateType t
  ; e' <- translateExpC pSrcLoc tenv cenv e t'' 
  ; u <- ucast srcLoc t'' t'
  ; return (TH.AppE u e')
  }
{-                                                         

   tenv, cenv |-^i e : t' ~> E
   for each i 
   l_i : t' -> t_i \in tenv
   tenv, cenv |-^c e_i : t_i ~> E_i
   |- t' <= t ~> u
  ------------------------------------- (CRecUM)
   tenv, cenv |-^c e@{[l=e]} : t ~> u e@{[l=E]}

-}
{-                                                         

   tenv, cenv |-^i e : forall a. t' ~> E
   for each i 
   l_i : forall a. C => t' -> t_i \in tenv
   \theta(t') = t    \theta is a substitution grounds t' to t
   \theta(C) \subseteq cenv
   tenv, cenv |-^c e_i : \theta(t_i) ~> E_i
  ------------------------------------- (CRecUP)
   tenv, cenv |-^c e@{[l=e]} : t ~> e@{[l=E]}

-}
translateExpC pSrcLoc tenv cenv (RecUpdate e fieldUpds) t = do -- todo poly version
  { (e',t') <- translateExpI pSrcLoc tenv cenv e
  ; if T.isMono t' 
    then do 
      { fieldExps' <- mapM (\fu -> translateFieldUpd pSrcLoc tenv cenv fu t) fieldUpds
      ; u  <- ucast pSrcLoc t' t
      ; return (TH.AppE u (TH.RecUpdE e' fieldExps'))
      } 
    else failWithSrcLoc pSrcLoc $ "Type checker can't to handle polymorphic record exp"
  }
{-                                                         

   tenv, cenv |-^i K : t1 -> ... -> tn -> t' ~> K
   for each i 
   l_i : t' -> t_i \in tenv
   tenv, cenv |-^c e_i : t_i ~> E_i
   |- t' <= t ~> u
  ------------------------------------- (CRecKM)
   tenv, cenv |-^c e@{[l=e]} : t ~> u e@{[l=E]}

-}
{-                                                         

   tenv, cenv |-^i e : forall a. t' ~> E
   for each i 
   l_i : forall a. C => t' -> t_i \in tenv
   \theta(t') = t    \theta is a substitution grounds t' to t
   \theta(C) \subseteq cenv
   tenv, cenv |-^c e_i : \theta(t_i) ~> E_i
  ------------------------------------- (CRecKP)
   tenv, cenv |-^c e@{[l=e]} : t ~> e@{[l=E]}

-}                                                    
translateExpC pSrcLoc tenv cenv (RecConstr n fieldUpds) t = do 
  -- todo poly version
  { n' <- translateQName n
  ; (r,ns) <- lookupQName n tenv
              
   -- check the parity and prepare to fill the missing optional filed with ()s 
   
  ; let missingFieldNames = findMissingFieldNames ns fieldUpds
  
  ; missingFieldNameTypeLookups <- mapM (\n -> lookupQName (UnQual n) tenv) missingFieldNames
  ; let missingFieldNameResultTypes = map (\(t,_) -> T.resultType t) missingFieldNameTypeLookups
  ; if T.isMono r
    then do  
      { let t'     = T.resultType r 
      ; fieldExps' <- mapM (\fu -> translateFieldUpd pSrcLoc tenv cenv fu t') fieldUpds
      ; u          <- ucast pSrcLoc t' t

                      -- make sure all the missing names are having optional result type 
                      -- and generate the expression

      ; missingFExps <- mapM (reconstructMissingFieldUpd pSrcLoc)
                        (zip missingFieldNames missingFieldNameResultTypes)
      ; return (TH.AppE u (TH.RecConE n' (fieldExps' ++ missingFExps)))
      }
    else failWithSrcLoc pSrcLoc "Type checker can't to handle polymorphic record exp"
  }
translateExpC pSrcLoc tenv cenv (Paren e) t = translateExpC pSrcLoc tenv cenv e t
translateExpC pSrcLoc tenv cenv e ty = failWithSrcLoc pSrcLoc ("Type checker can't handle expression : " ++ (prettyPrint e))
                
-- | Inference mode
translateExpI :: SrcLoc -> TyEnv -> ConstrEnv -> Exp -> TH.Q (TH.Exp, TH.Type)
{- 
  x : \forall \bar{a}. C => t \in tenv
   ----------------------------------(IVarP)
   tenv, cenv |-^i x : \forall \bar{a} . C => t ~> x

   x : t \in tenv
  -----------------------------------(IVarM)
   tenv, cenv |-^i x : t ~> x
-}
translateExpI pSrcLoc tenv cenv (Var qn) = do 
  { (ty,_) <- lookupQName qn tenv
  ; qName <- translateQName qn
  ; return (TH.VarE qName, ty)
  }
{-
   K : \forall \bar{a}. C => t \in tenv
   ----------------------------------(IConP)
   tenv, cenv |-^i K : \forall \bar{a} . C => t ~> K

   K : t \in tenv
  -----------------------------------(IConM)
   tenv, cenv |-^i K : t ~> K
-}
translateExpI pSrcLoc tenv cenv (Con qn) = do 
  { (ty,_) <- lookupQName qn tenv
  ; qName <- translateQName qn
  ; return (TH.ConE qName, ty)
  }
{-
  |- Lit : t
  --------------------------- (ILit)
  tenv, cenv |-^c Lit : t ~> Lit
-}
translateExpI pSrcLoc tenv cenv (Lit l) = do                                 
  { ql  <- translateLit l
  ; ty <- checkLitTy l
  ; return (TH.LitE ql, ty)
  }
{-                              
  (op : t1 -> t2 -> t3) \in tenv
  tenv,cenv |-^i e1 : t1' ~> E1
  tenv,cenv |-^i e2 : t2' ~> E2
  |- t1' <= t1 ~> u1
  |- t2' <= t2 ~> u2
 ----------------------------- (IBinOp)
  tenv,cenv |-^i e1 `op` e2 : t3 ~> (op (u1 E1)) (u2 E2)
-} 
translateExpI pSrcLoc tenv cenv (InfixApp e1 qop e2) = do
  { (e1',t1') <- translateExpI pSrcLoc tenv cenv e1 
  ; (e2',t2') <- translateExpI pSrcLoc tenv cenv e2
  ; (qn, op') <- case qop of
          { QVarOp qn -> do 
               { n <- translateQName qn 
               ; return (qn, TH.VarE n)
               }
          ; QConOp qn -> do 
               { n <- translateQName qn
               ; return (qn, TH.ConE n)
               }
          }
  ; (ty',_) <- lookupQName qn tenv -- TH type
  ; case ty' of
    { TH.AppT (TH.AppT TH.ArrowT t1) (TH.AppT (TH.AppT TH.ArrowT t2) t3) -> do
         { u1 <- ucast pSrcLoc t1' t1 
         ; u2 <- ucast pSrcLoc t2' t2
         ; return (TH.AppE (TH.AppE op' (TH.AppE u1 e1')) (TH.AppE u2 e2'), t3)
         }
    ; TH.ForallT tyVarBnds cxt t -> failWithSrcLoc pSrcLoc $ ((prettyPrint qop) ++ ":" ++ (TH.pprint ty') ++ " is still polymorphic, please give it a type annotation.") 
    ; _ -> failWithSrcLoc pSrcLoc ((prettyPrint qop) ++ ":" ++ (TH.pprint ty') ++ " is not a binary op")
    }
  }
{-                                                
  f : forall \bar{a}. c => t1' -> ... tn' -> r  \in tenv
   tenv,cenv |-^i ei : ti ~> Ei
   \bar{a} |- ti <: ti' ==> Di
   S = solve(D1++ ... ++Dn, r)
   |- ti <= S(ti') ~> ui
   S(c) \subseteq cenv
  ----------------------------------------- (IEAppInf)
   tenv,cenv |-^i f e1 ... en : S(r) ~>
      f (u1 E1) ... (un En)
-}
translateExpI pSrcLoc tenv cenv e@(App e1 e2) = do 
  { mb <- appWithPolyFunc tenv e 
  ; case mb of
      { Just (f, es) -> do 
           { (f', tyF) <- translateExpI pSrcLoc tenv cenv f
           ; e't's <- mapM (translateExpI pSrcLoc tenv cenv) es
           ; case tyF of
             { TH.ForallT tyVarBnds ctxt t -> do
                  { let as  = map T.getTvFromTvb tyVarBnds
                        (ts, r) = T.breakFuncType t (length e't's)
                        es' = map fst e't's
                        ts' = map snd e't's
                        ds  = concatMap (\(t,t') -> genSubtypeConstrs as [] t t') (zip ts' ts)
                  ; s <- solveSubtypeConstrs ds r
                  {- ; TH.runIO ((putStrLn "====") >> putStrLn (prettyPrint e) >> (putStrLn ("s" ++ (show s))))
                  ; TH.runIO (putStrLn ("ts':" ++ (TH.pprint ts')))
                  ; TH.runIO (putStrLn ("t:" ++ (TH.pprint t)))
                  ; TH.runIO (putStrLn ("ds:" ++ (show ds)))
                  ; TH.runIO (putStrLn ("r:" ++ (TH.pprint r))) -}
                  ; if deducible (cxtToConstrs $ T.applySubst s ctxt) cenv
                    then do 
                      { -- TH.runIO (putStrLn (TH.pprint (T.applySubst s t)))
                      ; us <- mapM (\(t,t') -> inferThenUpCast pSrcLoc t t' -- t might be still polymorphic                               
                                   ) (zip ts' (map (T.applySubst s) ts))

                      ; let ues = map (\(u,e) -> TH.AppE u e) (zip us es')
                      ; return (foldl TH.AppE f' ues, T.applySubst s r)
                      }
                    else failWithSrcLoc pSrcLoc $ "Unable to deduce " ++ (TH.pprint (T.applySubst s ctxt)) ++ "from the context " ++ show cenv 
                  }
             ; _ -> failWithSrcLoc pSrcLoc (TH.pprint tyF ++ " is not polymorphic.")
             }
           }
      ; _ -> do 
{-                                               
   tenv,cenv |-^i e1 : t1 -> t2 ~> E1 
   tenv,cenv |-^i e2 : t1' ~> E2
   |- t1' <= t1 ~> u1
  ----------------------------------------- (IEApp) 
    tenv,cenv |-^c e1 e2 : t2 ~> E1 (u1 E2)
-}
-- translateExpI tenv cenv (App e1 e2) = do 
           { (e1', t12) <- translateExpI pSrcLoc tenv cenv e1
           ; case t12 of
             { TH.AppT (TH.AppT TH.ArrowT t1) t2 -> do 
                  { (e2', t1') <- translateExpI pSrcLoc tenv cenv e2
                  ; u1 <- ucast pSrcLoc  t1' t1
                  ; return (TH.AppE e1' (TH.AppE u1 e2'), t2)
                  }
             ; TH.ForallT tyVarBnds cxt t -> failWithSrcLoc pSrcLoc ((prettyPrint e1) ++ ":" ++ (TH.pprint t12) ++ " is still polymorphic, please give it a type annotation.")                                             
             ; _ -> failWithSrcLoc pSrcLoc ((prettyPrint e1) ++ ":" ++ (TH.pprint t12) ++ " is not a function.")
             }
           }
      }
  }
{-                                    
  tenv |-^i e : t ~> E
-------------------------- (INeg)
  tenv |-^i -e : t ~> -E
-}
translateExpI pSrcLoc tenv cenv (NegApp e) = do
  { (e',t) <- translateExpI pSrcLoc tenv cenv e
  ; return (TH.AppE (TH.VarE (TH.mkName "GHC.Num.negate")) e',t)
  }
translateExpI pSrcLoc tenv cenv (Let binds e) = failWithSrcLoc pSrcLoc $ "can't handle let bindings yet."
{- tenv, cenv |-^c e1 : Bool ~> E1
   tenv, cenv |-^i e2 : t2 ~> E2
   tenv,cenv |-^i e3 : t3 ~> E3
------------------------------------------------------------
tenv, cenv |-^i if e1 then e2 else e3 : (t2|t3) ~> if E1 then E2 else E3
-}
translateExpI pSrcLoc tenv cenv (If e1 e2 e3) = do
  { e1' <- translateExpC pSrcLoc tenv cenv e1 (TH.ConT (TH.mkName "Bool")) -- (TyCon (UnQual (Ident "Bool")))
  ; (e2',t2) <- translateExpI pSrcLoc tenv cenv e2 
  ; (e3',t3) <- translateExpI pSrcLoc tenv cenv e3 
  ; return (TH.CondE e1' e2' e3', TH.AppT (TH.AppT (TH.ConT (TH.mkName "Choice")) t2) t3) 
  }
{-         
tenv |-^i e1 : t1 ~> E1
tenv |-^i e2 : t2 ~> E2 
--------------------------------------
tenv |-^i (e1,e2) : (t1,t2) ~> (E1,E2)
-}
translateExpI pSrcLoc tenv cenv (Tuple boxed []) = failWithSrcLoc pSrcLoc ("empty tuple expxpression")
translateExpI pSrcLoc tenv cenv (Tuple boxed [e]) = failWithSrcLoc pSrcLoc ("singleton tuple expression")
translateExpI pSrcLoc tenv cenv (Tuple boxed [e1,e2]) = do 
  { (e1',t1') <- translateExpI pSrcLoc tenv cenv e1
  ; (e2',t2') <- translateExpI pSrcLoc tenv cenv e2
  ; let t = TH.AppT (TH.AppT (TH.TupleT 2) t1') t2'
  ; return (TH.TupE [e1',e2'], t)
  }
translateExpI pSrcLoc tenv cenv (Tuple boxed (e:es)) = do                                             
  { (e1',t1') <- translateExpI pSrcLoc tenv cenv e
  ; (e2',t2') <- translateExpI pSrcLoc tenv cenv (Tuple boxed es)
  ; let t  =  TH.AppT (TH.AppT (TH.TupleT 2) t1') t2'
  ; return (TH.TupE [e1',e2'], t)
  } 
{-                                               
  tenv, cenv |-^c e : t ~> E
 ------------------------ (ITApp)
  tenv, cenv |-^i e :: t : t ~> E
-}                                               
translateExpI pSrcLoc tenv cenv e1@(ExpTypeSig srcLoc e t) =  do
  { t' <- translateType t
  ; e' <- translateExpC pSrcLoc tenv cenv e t'
  ; return (e', t')
  }
{-
   tenv U {(x:t1)}, cenv |-^i e : t2 ~> E
   -----------------------------------------(IAbsVA)
   tenv, cenv |-^i \x::t1 -> e : t1 -> t2 ~> \x -> E
-}
translateExpI pSrcLoc tenv cenv e1@(Lambda srcLoc [(PParen (PatTypeSig srcLoc' (PVar x) t1))] e) = do
  { t1' <- translateType t1
  ; let tenv' = addTyEnv x t1' tenv
  ; (e',t2) <- translateExpI srcLoc tenv' cenv e
  ; x' <- translateName x
  ; return ((TH.LamE [TH.VarP x'] e'), TH.AppT (TH.AppT TH.ArrowT t1') t2)
  }
{-
---------------------------------------------
 tenv |-^i \x -> e : ~> error 
-}
translateExpI pSrcLoc tenv cenv e1@(Lambda srcLoc _ e) =  failWithSrcLoc srcLoc $ "Type inferencer failed: unannotated lambda expression : \n " ++ (prettyPrint e1)
translateExpI pSrcLoc tenv cenv e1@(Case _ _) = failWithSrcLoc pSrcLoc $ "Type inferencer failed: unannotated case expression : \n" ++ (prettyPrint e1)  
translateExpI pSrcLoc tenv cenv (Paren e) = translateExpI pSrcLoc tenv cenv e                                                      
{-                                                         

   tenv, cenv |-^i e : t' ~> E
   for each i 
   l_i : t' -> t_i \in tenv
   tenv, cenv |-^c e_i : t_i ~> E_i
  ------------------------------------- (IRecUM)
   tenv, cenv |-^i e@{[l=e]} : t' ~> e@{[l=E]}

-}
{-                                                         

   tenv, cenv |-^i e : forall a. t' ~> E
   for each i 
   l_i : forall a. C => t' -> t_i \in tenv
   \theta(t') = t    \theta is a substitution grounds t' to t
   \theta(C) \subseteq cenv
   tenv, cenv |-^c e_i : \theta(t_i) ~> E_i
  ------------------------------------- (IRecUP)
   tenv, cenv |-^i e@{[l=e]} : t ~> e@{[l=E]}

-}
translateExpI pSrcLoc tenv cenv (RecUpdate e fieldUpds) = do
  { (e',t) <- translateExpI pSrcLoc tenv cenv e
  ; if T.isMono t 
    then do 
      { fieldExps' <- mapM (\fu -> translateFieldUpd pSrcLoc tenv cenv fu t) fieldUpds
      ; return (TH.RecUpdE e' fieldExps', t)
      }
    else failWithSrcLoc pSrcLoc $ "Type inferencer can't to handle polymorphic record exp"
  }
                                                  
{-                                                         

   tenv, cenv |-^i K : t1 -> ... -> tn -> t' ~> K
   for each i 
   l_i : t' -> t_i \in tenv
   tenv, cenv |-^c e_i : t_i ~> E_i
  ------------------------------------- (IRecKM)
   tenv, cenv |-^i e@{[l=e]} : t' ~> e@{[l=E]}

-}
{-                                                         

   tenv, cenv |-^i e : forall a. t' ~> E
   for each i 
   -- we might need to build the theta from the individual e_i
  ------------------------------------- (IRecKP)
   tenv, cenv |-^c e@{[l=e]} : t ~> e@{[l=E]}

-}                                                                                               
                                                  
translateExpI pSrcLoc tenv cenv (RecConstr n fieldUpds) = do
  -- todo polymoprhic
  { n' <- translateQName n
  ; (r,ns) <- lookupQName n tenv
             
   -- check the parity and prepare to fill the missing optional filed with ()s 

  ; let missingFieldNames = findMissingFieldNames ns fieldUpds
  ; missingFieldNameTypeLookups <- mapM (\n -> lookupQName (UnQual n) tenv) missingFieldNames
  ; let missingFieldNameResultTypes = map (\(t,_) -> T.resultType t) missingFieldNameTypeLookups             
  ; if T.isMono r
    then do 
      { let t' = T.resultType r
      ; fieldExps' <- mapM (\fu -> translateFieldUpd pSrcLoc tenv cenv fu t') fieldUpds
                      -- make sure all the missing names are having optional result type 
                      -- and generate the expression
      ; missingFExps <- mapM (reconstructMissingFieldUpd pSrcLoc)
                        (zip missingFieldNames missingFieldNameResultTypes)
                      
      ; return (TH.RecConE n' (fieldExps' ++ missingFExps),t')
      }
    else failWithSrcLoc pSrcLoc $ "Type inferencer can't unable to handle polymorphic record exp"
  }
translateExpI pSrcLoc tenv cenv e = failWithSrcLoc pSrcLoc ("Type inferencer can't handle expression : \n" ++ (prettyPrint e))



-- translate the field update
translateFieldUpd :: SrcLoc -> TyEnv -> ConstrEnv -> FieldUpdate -> TH.Type -> TH.Q TH.FieldExp
translateFieldUpd pSrcLoc tenv cenv (FieldUpdate qname e) t = do 
  { (t',_) <- lookupQName qname tenv
  ; if T.isMono t'
    then do 
      { let r = T.resultType t'
      ; e' <- translateExpC pSrcLoc tenv cenv e r
      ; n' <- translateQName qname
      ; return (n',e')
      }
    else failWithSrcLoc pSrcLoc $ "Type inferencer can't handle polymorphic record exp"
  }

-- find the missing field names 
findMissingFieldNames :: [Name] -> [FieldUpdate] -> [Name]
findMissingFieldNames allNames fieldUpds =
  let names = foldl (\names fu -> case fu of
                        { FieldUpdate qn _ -> 
                             let n = case qn of {UnQual x-> x; Qual mn x -> x; e -> error (show e)}
                             in if n `elem` names
                                then names
                                else names ++ [n] 
                        ; _ -> names }) [] fieldUpds
  in filter (\n -> not (n `elem` names)) allNames

-- reconstruct the missing field name expression from ()s
reconstructMissingFieldUpd :: SrcLoc -> (Name, TH.Type) -> TH.Q TH.FieldExp
reconstructMissingFieldUpd pSrcLoc (n,t) =  do 
  { u  <- ucast pSrcLoc (TH.ConT $ TH.mkName "()") t 
  ; n' <- translateName n  
  ; return $ (n', TH.AppE u (TH.ConE $ TH.mkName "()"))
  }


-- | extract the type annotations from a pattern
-- | | (x :: t) | = t
-- | | (p1,p2) | = (|p1|, |p2|)
patStripT :: SrcLoc -> TyEnv -> Pat -> TH.Q TH.Type 
-- for haskell-src-exts 1.14 + 
patStripT pSrcLoc _ (PTuple box []) = failWithSrcLoc pSrcLoc "empty tuple pattern encountered"
patStripT pSrcLoc tenv (PTuple box [p]) = patStripT pSrcLoc tenv p
patStripT pSrcLoc tenv (PTuple box (p:ps)) = do
  { t <- patStripT pSrcLoc tenv p
  ; ts <- mapM (patStripT pSrcLoc tenv) ps
  ; return $ foldl (\t1 t2 -> TH.AppT (TH.AppT (TH.TupleT 2) t1) t2) t ts
  }
-- for haskell-src-exts < 1.14
{-
patStripT (PTuple []) = fail "empty tuple pattern encountered"
patStripT (PTuple [p]) = patStripT p
patStripT (PTuple (p:ps)) = do
  { t <- patStripT p
  ; ts <- mapM patStripT ps
  ; return $ foldl (\t1 t2 -> TH.AppT (TH.AppT (TH.TupleT 2) t1) t2) t ts
  }
-}
patStripT pSrcLoc tenv (PatTypeSig srcLoc (PVar n) t) = translateType t                        
patStripT pSrcLoc tenv (PParen p) = patStripT pSrcLoc tenv p
patStripT pSrcLoc tenv (PApp qname ps) = do 
  { ts <- mapM (patStripT pSrcLoc tenv) ps -- todo check ts with the type of qName : t \in tenv
  ; (ty,_) <- lookupQName qname tenv 
  ; T.lineUpTypes pSrcLoc ty ts
  }
patStripT pSrcLoc tenv (PRec qname fps) = do                                 
  { (ty,_) <- lookupQName qname tenv 
  ; return $ T.resultType ty 
  }

patStripT pSrcLoc _ p = failWithSrcLoc  pSrcLoc ("unhandle pattern " ++ (prettyPrint p) ++ (show p))

-- | remove the type annotation from a pattern 
-- | { x :: t } = x
-- | { (p1,p2) } = ({p1},{p2})
patStripP :: SrcLoc ->  Pat -> TH.Q TH.Pat
patStripP pSrcLoc (PTuple box []) = failWithSrcLoc  pSrcLoc "empty tuple pattern encountered"
patStripP pSrcLoc (PTuple box [p]) = patStripP pSrcLoc p
patStripP pSrcLoc (PTuple box (p:ps)) = do
  { q <- patStripP pSrcLoc p
  ; qs <- mapM (patStripP pSrcLoc) ps
  ; return $ foldl (\p1 p2 -> TH.TupP [p1, p2]) q qs
  }
patStripP pSrcLoc (PatTypeSig srcLoc (PVar n) t) = do 
  { n' <- translateName n
  ; return (TH.VarP n')
  } 
patStripP pSrcLoc (PParen p) = patStripP pSrcLoc p                                          
patStripP pSrcLoc (PApp qname ps) = do 
  { qs <- mapM (patStripP pSrcLoc) ps
  ; name' <- translateQName qname 
  ; return (TH.ConP name' qs)
  }
patStripP pSrcLoc (PRec qname fps) = do                            
  { name' <- translateQName qname
  ; fps' <- mapM (\(PFieldPat qname p) -> do
                     { p' <- patStripP pSrcLoc p
                     ; name' <- translateQName qname
                     ; return (name', p') 
                     }) fps
  ; return (TH.RecP name' fps')
  }
                   
                            
patStripP pSrcLoc p = failWithSrcLoc pSrcLoc ("unhandle pattern " ++ (prettyPrint p) ++ (show p))

{-
-- | build type environment from a pattern
-- | [ x :: t ] = { (x, t) }
-- | [ (p1,p2) ] = [p1] ++ [p2]
patTEnv :: Pat -> TH.Q TyEnv
patTEnv (PTuple box []) = fail "empty tuple pattern encountered"
patTEnv (PTuple box [p]) = patTEnv p                      
patTEnv (PTuple box (p:ps)) = do
  { e <- patTEnv p
  ; es <- mapM patTEnv ps
  ; return $ foldl unionTyEnv e es
  }
patTEnv (PatTypeSig srcLoc (PVar n) t) = do
  { t' <- translateType t
  ; return (addTyEnv n t'  M.empty)
  }
patTEnv (PParen p) = patTEnv p  
patTEnv (PApp qname ps) = do 
  { es <- mapM patTEnv ps
  ; return $ foldl unionTyEnv M.empty es
  }
patTEnv p = fail ("unhandle pattern " ++ (prettyPrint p) ++ (show p))   
-}                                             
                                             
-------------------------------------------- helper functions for nested pattern matching -------------------------
-- | extended patTEnv 

patEnv :: SrcLoc -> TyEnv -> TH.Type -> Pat -> TH.Q (TyEnv, TH.Exp, TH.Exp, TH.Pat) -- the codomain type env is not generated
patEnv pSrcLoc te t (PTuple box []) = failWithSrcLoc pSrcLoc "Pattern Environment construction failed, an empty tuple pattern encountered."
patEnv pSrcLoc te t (PTuple box [p]) = patEnv pSrcLoc te t p
{-
t1,p1 |- tenv1, gd1, ex1, dom1, cod1
t2,p2 |- tenv2, gd2, ex2, dom2, cod2
------------------------------------------------------------------------------
(t1,t2), (p1,p2) |- tenv1 U tenv2, \(x,y) -> (gd1 x && gd2 y),  \(x,y) -> (ex1 x, ex2 y), (dom1,dom2), (cod1,cod2)
-}
patEnv pSrcLoc te t (PTuple box (p:ps)) = do
  { let ts = unTupleTy t
  ; xs <- mapM (\ (t',p) -> patEnv pSrcLoc te t' p) (zip ts (p:ps))
  ; names' <- T.newNames (length (p:ps)) "x"
  ; let (tenv, gds, exs, ps') = foldl (\(tenv,gds,exs,qs) (tenv',gd,ex,q) -> 
                                        (tenv `unionTyEnv` tenv', 
                                         gds ++ [gd], 
                                         exs ++ [ex],
                                         qs ++ [q])) (M.empty,[],[],[]) xs
        p'                    = TH.TupP ps'
        vps                   = map TH.VarP names'
        ves                   = map TH.VarE names'
        gdes                  = map (\(gd,ve) -> TH.AppE gd ve) (zip gds ves)
        gd                    = TH.LamE [TH.TupP vps] (TH.AppE (TH.VarE $ TH.mkName "and") (TH.ListE gdes))
        exes                  = map (\(ex,ve) -> TH.AppE ex ve) (zip exs ves)
        ex                    = TH.LamE [TH.TupP vps] (TH.TupE exes)
        
  ; return  (tenv, gd, ex, p')
  }
patEnv pSrcLoc te t (PatTypeSig srcLoc (PVar n) t') = do
  { t'' <- translateType t'
  ; if (t'' == t) 
    then do 
{- t, (x :: t) |- { (x, t) },  (\x -> True), id, x, t -}
      { let tenv = addTyEnv n t M.empty
            gd   = TH.LamE [TH.VarP (TH.mkName "x")] (TH.ConE (TH.mkName "True"))
            ex   = TH.LamE [TH.VarP (TH.mkName "x")] (TH.VarE (TH.mkName "x"))
      ; n' <- translateName n 
      ; let p' = TH.VarP n'
      ; return (tenv, gd, ex, p')
      }
    else do 
{-
 t' <= t ~> d
-----------------------------------------
t, (x :: t') |- { (x, t') },  isJust . d,  fromJust . d , x, t'
-}
      { d <- dcast pSrcLoc t'' t
      ; let tenv = addTyEnv n t'' M.empty
            gd   = TH.LamE [TH.VarP (TH.mkName "x")] (TH.AppE (TH.VarE $ TH.mkName "Data.Maybe.isJust") (TH.AppE d (TH.VarE $ TH.mkName "x")))
            ex   = TH.LamE [TH.VarP (TH.mkName "x")] (TH.AppE (TH.VarE $ TH.mkName "Data.Maybe.fromJust") (TH.AppE d (TH.VarE $ TH.mkName "x")))
      ; n' <- translateName n 
      ; let p' = TH.VarP n'
      ; return (tenv, gd, ex, p')
      }
  }
patEnv pSrcLoc te t (PParen p) = patEnv pSrcLoc te t p                                           
{-
K :: t1 -> ... -> tn -> t 
t_i, p_i |- tenv_i, gd_i, ex_i, dom_i, cod_i
------------------------------------------------------------------------------------------------------------------------------------------------
t, K [p] |- U tenv_i, \(K [p']) -> gd_1 p_1' && ... && gd_n p_n', \(K [p']) -> (ex1 p'1, ex2 p_2', ... ), (dom_1,...,dom_n), (cod_1,...,cod_i)
-}
patEnv pSrcLoc te t p@(PApp qname ps) = do
  { (t',_) <- lookupQName qname te
  ; let ts = T.argsTypes t'
        r  = T.resultType t'
   -- todo check r == t?
  ; if (length ps == length ts)
    then do 
      { let tps = zip ts ps 
      ; qname' <- translateQName qname
      ; xs <- mapM (\(t,p) -> patEnv pSrcLoc te t p) tps
      ; names' <- T.newNames (length ps) "x"
      ; let (tenv, gds, exs, ps') = foldl (\(tenv,gds,exs,qs) (tenv',gd,ex,q) -> 
                                           (tenv `unionTyEnv` tenv', 
                                            gds ++ [gd], 
                                            exs ++ [ex],
                                            qs ++ [q])) (M.empty,[],[],[]) xs
            p'                    = TH.TupP ps'
            vps                   = map TH.VarP names'
            ves                   = map TH.VarE names'
            gdes                  = map (\(gd,ve) -> TH.AppE gd ve) (zip gds ves)
            gd                    = TH.LamE [TH.ConP qname' vps] (TH.AppE (TH.VarE $ TH.mkName "and") (TH.ListE gdes))
            exes                  = map (\(ex,ve) -> TH.AppE ex ve) (zip exs ves)
            ex                    = TH.LamE [TH.ConP qname' vps] (TH.TupE exes)
      ; return (tenv, gd, ex, p')
      }
    else failWithSrcLoc pSrcLoc ("Fail to construct pattern environment from the pattern " ++ (prettyPrint p) ++ " the number of pattern args is wrong.")
  }
{-                                
l_i :: t -> t_i 
t_i, p_i |- tenv_i, gd_i, ex_i, dom_i, cod_i
---------------------------------------
t, K { [l=p] } |- U tenv_i, \x -> gd_1 (l_1 x)  && ... && gd_n (l_n x), \x ->(ex1 (l_1 x), ..., (exn (l_n x) )), (dom_1,...,dom_n), (cod_1,...,cod_i)

-}
patEnv pSrcLoc te t p@(PRec qname fps) = do
  { (t', ns) <- lookupQName qname te
  ; let ts = T.argsTypes t'
        r  = T.resultType t'
        names = map (\(PFieldPat l p) -> l) fps
        ps    = map (\(PFieldPat l p) -> p) fps
  ; ats <- mapM (\l -> lookupQName l te) names
  ; let ts = map (T.resultType . fst) ats
  ; xs  <- mapM (\(t,p) -> patEnv  pSrcLoc te t p) (zip ts ps)
  ; nn  <- TH.newName "x"
  ; names' <- mapM translateQName names
  ; let (tenv, gds, exs, ps') = foldl (\(tenv, gds, exs, qs) (tenv', gd,ex,q) ->
                                        (tenv `unionTyEnv` tenv',
                                         gds ++ [gd],
                                         exs ++ [ex],
                                         qs ++ [q])) (M.empty,[],[],[]) xs
        p'                    = TH.TupP ps' 
        gdes                  = map (\(l,gd) ->  TH.AppE gd (TH.AppE (TH.VarE l) (TH.VarE nn))) (zip names' gds)
        gd                    = TH.LamE [TH.VarP nn] (TH.AppE (TH.VarE $ TH.mkName "and") (TH.ListE gdes))
        exes                  = map (\(l,ex) ->  TH.AppE ex (TH.AppE (TH.VarE l) (TH.VarE nn))) (zip names' exs)
        ex                    = TH.LamE [TH.VarP nn] (TH.TupE (exes))
  ; return (tenv, gd, ex, p')
  } 
patEnv pSrcLoc te t p = failWithSrcLoc pSrcLoc ("Fail to construct pattern environment from the pattern " ++ (prettyPrint p) ++ (show p))
             
{-                
joinAppEWith :: TH.Exp -> TH.Exp -> TH.Exp -> TH.Exp
joinAppEWith e1 e2 e3 = 
  TH.LamE [TH.TupP [ TH.VarP (TH.mkName "x"), TH.VarP (TH.mkName "y")]] (TH.AppE 
                                                                         (TH.AppE 
                                                                          e1
                                                                          (TH.AppE e2 (TH.VarE (TH.mkName "x")))) 
                                                                         (TH.AppE e3 (TH.VarE (TH.mkName "y"))))
-}
-- (t1,t2,t3) -> [t1,t2,t3]            
unTupleTy :: TH.Type -> [TH.Type]
unTupleTy (TH.AppT (TH.AppT (TH.TupleT 2) t1) t2) = 
  let ts = unTupleTy t1
  in ts ++ [t2]
unTupleTy t = [t]     
                    

---------------- helper functions for local type inference ------------------------

-- test whether a application expression is started with an polymoprhic f
--  if so, the f and the args are seperated and returned as a pair
appWithPolyFunc :: TyEnv -> Exp -> TH.Q (Maybe (Exp, [Exp]))
appWithPolyFunc tenv e = 
  case S.flatten e of
    { l@((Var f):es) -> do
         { (t,_) <- lookupQName f tenv
         ; if T.isPoly t
           then return (Just (Var f, es))
           else return Nothing
         }
    ; _ -> return Nothing }
           

inferThenUpCast :: SrcLoc -> TH.Type -> TH.Type -> TH.Q TH.Exp
inferThenUpCast pSrcLoc (TH.ForallT tvbs ctxt t1) t2 | T.isMono t2 = do -- the arg type can be still poly, we apply local inference again
  { let as  = map T.getTvFromTvb tvbs 
        ts1 = T.argsTypes t1
        ts2 = T.argsTypes t2
        r1 = T.resultType t1
        ds = concatMap (\(t,t') -> genSubtypeConstrs as [] t t') (zip ts1 ts2)
  ; s <- solveSubtypeConstrs ds r1
  ; ucast pSrcLoc (T.applySubst s t1) t2
  } 
inferThenUpCast pSrcLoc t1 t2 = ucast pSrcLoc t1 t2                                                              



xh :: QuasiQuoter 
xh = QuasiQuoter { quoteExp = undefined, -- not in used
                   quotePat = undefined, -- not in used
                   quoteType = undefined, -- not in used
                   quoteDec = xhDecls
                 }
     

     

{-
import Language.Haskell.TH as TH
$(TH.stringE . show =<< TH.reify (TH.mkName "()"))


parseDeclWithMode pmScopedTyVar "f x = g f x"
-}