{-# LANGUAGE MultiParamTypeClasses,TemplateHaskell,QuasiQuotes #-}

module Language.XHaskell.Error where

import qualified Language.Haskell.TH as TH
import Language.Haskell.Exts.Syntax




failWithSrcLoc :: SrcLoc -> String -> TH.Q a
failWithSrcLoc srcLoc mesg = do 
  { loc <- TH.location
  ; let (line,col) = TH.loc_start loc
        col' | line == 0 = col
             | otherwise = 0
  ; fail $ "Error at line " ++ (show (line + (srcLine srcLoc))) ++ ", column " ++ (show (col' + (srcColumn srcLoc))) ++ ":\n" ++ mesg 
  }
                                