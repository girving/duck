{-# LANGUAGE PatternGuards, FlexibleInstances, StandaloneDeriving #-}

module PrettyLir
 (
 ) where

import Data.Map (Map)
import qualified Data.Map as Map

import Lir
import ParseOps
import qualified Ptrie
import Pretty
import Prims
import Type
import TypedValue
import Var

-- Pretty printing for Lir

instance Pretty Prog where
  pretty' prog = vcat $
       [pretty "-- datatypes"]
    ++ [datatype (dataName d) (dataTyVars d) (dataInfo d) 0 | d <- Map.elems (progDatatypes prog)]
    ++ [pretty "-- functions"]
    ++ [pretty $ function v o | (v,os) <- Map.toList (progOverloads prog), let Left ol = Ptrie.get os, o <- ol]
    ++ [pretty "-- overloads"]
    ++ [pretty (progOverloads prog)]
    ++ [pretty "-- definitions"]
    ++ [pretty $ definition d | d <- progDefinitions prog]
    where
    function v o = nested (v <+> "::") o
    definition (Def _ vl e) = nestedPunct '=' (punctuate ',' vl) e
    datatype t args (DataAlgebraic []) =
      "data" <+> prettyap t args
    datatype t args (DataAlgebraic l) =
      nested ("data" <+> prettyap t args <+> "of") $
        vcat $ map (\(c,args) -> prettyop c args) l
    datatype t args (DataPrim _) =
      "data" <+> prettyap t args <+> "of <opaque>"

instance Pretty (Map Var Overloads) where
  pretty' info = vcat [pr f tl o | (f,p) <- Map.toList info, (tl,o) <- Ptrie.toList p] where
    pr f tl o = nested (f <+> "::") (o{ overArgs = zip (map fst (overArgs o)) tl })

instance (IsType t, Pretty t) => Pretty (Overload t) where
  pretty' (Over _ a r _ Nothing) = 1 #> hsep (map (<+> "->") a) <+> r
  pretty' o@(Over _ _ _ v (Just e)) = sep [pretty' o{ overBody = Nothing },
    '=' <+> (1 #> hsep (map (<+> "->") v)) <+> e]

instance Pretty Exp where
  pretty' (ExpSpec e t) = 2 #> guard 2 e <+> "::" <+> t
  pretty' (ExpLet v e body) = 1 #>
    "let" <+> v <+> '=' <+> pretty e <+> "in" $$ pretty body
  pretty' (ExpCase v pl d) = 1 #>
    nested ("case" <+> v <+> "of")
      (vcat (map arm pl ++ def d)) where
    arm (c, vl, e) = prettyop c vl <+> "->" <+> pretty e
    def Nothing = []
    def (Just e) = ["_ ->" <+> pretty e]
  pretty' (ExpAtom a) = pretty' a
  pretty' (ExpApply e1 e2) = uncurry prettyop (apply e1 [e2])
    where apply (ExpApply e a) al = apply e (a:al)
          apply e al = (e,al)
  pretty' (ExpCons d c args) = case dataInfo d of
    DataAlgebraic conses -> prettyop (fst $ conses !! c) args
    DataPrim _ -> error ("ExpCons with non-algebraic datatype"++show (quoted d))
  pretty' (ExpPrim p el) = prettyop (V (primString p)) el
  pretty' (ExpLoc _ e) = pretty' e
  --pretty' (ExpLoc l e) = "{-@" <+> show l <+> "-}" <+> pretty' e

instance Pretty Atom where
  pretty' (AtomLocal v) = pretty' v
  pretty' (AtomGlobal v) = pretty' v
  pretty' (AtomVal (Any t v)) = prettyval t v
