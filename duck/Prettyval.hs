{-# LANGUAGE PatternGuards, TypeSynonymInstances, FlexibleInstances, StandaloneDeriving #-}
{-# OPTIONS -fno-warn-orphans #-}
-- | Pretty printing for duck values and Lir

module Prettyval
  ( prettyval
  ) where

import Prelude hiding (lookup)
import Data.Map (Map)
import qualified Data.Map as Map

import Var
import Util
import Type
import Prims
import Pretty
import ParseOps
import SrcLoc
import Memory
import Value
import Lir
import qualified Ptrie

-- | Pretty printing for values

prettyval :: Datatypes -> TypeVal -> Value -> Doc'
prettyval _ t v | t == typeInt = pretty' (unsafeUnvalue v :: Int)
prettyval _ t v | t == typeChar = pretty' (unsafeUnvalue v :: Char)
prettyval denv (TyCons (V "List") [t]) v = pretty' $
  brackets $ 3 #> punctuate ',' (map (prettyval denv t) v')
  where v' = unsafeUnvalue v :: [Value]
prettyval _ (TyCons (V "Type") [t]) _ = pretty' t
prettyval denv (TyFun _) v = prettyfun denv (unsafeUnvalue v :: FunValue)
prettyval denv (TyCons (V "IO") [t]) v = prettyio denv t (unsafeUnvalue v :: IOValue)
prettyval denv (TyCons tc args) v = case Map.lookup tc denv of
  Just (Data _ _ vl conses _) -> prettyop c (zipWith (prettyval denv) tl' values) where
    (L _ c,tl) = conses !! unsafeTag v
    tenv = Map.fromList (zip vl args)
    tl' = map (substVoid tenv) tl
    values = unsafeUnvalConsN (length tl) v
  Nothing -> error ("unbound datatype "++show tc++" in prettyval")
prettyval _ TyVoid _ = error "found an impossible Void value in prettyval"

instance Pretty (Datatypes, TypeVal, Value) where
  pretty' (denv,t,v) = 2 #> prettyval denv t v <+> "::" <+> t

prettyfun :: Datatypes -> FunValue -> Doc'
prettyfun denv (ValClosure v types args) = prettyop v (zipWith (prettyval denv) types args)
prettyfun denv (ValDelay e _) = prettyop "delay" [(denv,e)]

--instance Pretty (Datatypes, FunValue) where
--  pretty' (denv, v) = prettyfun denv v

prettyio :: Datatypes -> TypeVal -> IOValue -> Doc'
prettyio denv t (ValLiftIO v) = pretty' (denv,t,v)
prettyio _ _ (ValPrimIO p []) = pretty' $ primString p
prettyio denv _ (ValPrimIO IOPutChar [c]) = prettyop (V "ioPutChar") [prettyval denv typeChar c]
prettyio denv _ (ValBindIO v t d e _) = 0 #> v <+> "<-" <+> prettyio denv t d $$ pretty (denv,e)
prettyio _ _ (ValPrimIO _ _) = pretty' "<unknown-prim-io>"

--instance Pretty (Datatypes, TypeVal, IOValue) where
--  pretty' (denv,t,v) = prettyio denv t v

instance (Ord k, Pretty k) => Pretty (Datatypes, Map k TypeVal, Map k Value) where
  pretty' (denv,t,v) = pretty' $ Map.intersectionWith (\t v -> (denv,t,v)) t v

-- Pretty printing for Lir

instance Pretty Prog where
  pretty' prog = vcat $
       [pretty "-- datatypes"]
    ++ [datatype (L l t) vl c 0 | Data t l vl c _ <- Map.elems (progDatatypes prog)]
    ++ [pretty "-- functions"]
    ++ [pretty $ function v o | (v,os) <- Map.toList (progFunctions prog), o <- os]
    ++ [pretty "-- overloads"]
    ++ [pretty (denv, progOverloads prog)]
    ++ [pretty "-- definitions"]
    ++ [pretty $ definition d | d <- progDefinitions prog]
    where
    denv = progDatatypes prog
    function v o = nested (v <+> "::") (denv,o)
    definition (Def vl e) = nestedPunct '=' (punctuate ',' vl) (denv,e)
    datatype t args [] =
      "data" <+> prettyap t args
    datatype t args l =
      nested ("data" <+> prettyap t args <+> "of") $
        vcat $ map (\(c,args) -> prettyop c args) l

instance Pretty (Datatypes, Map Var Overloads) where
  pretty' (denv,info) = vcat [pr f tl o | (f,p) <- Map.toList info, (tl,o) <- Ptrie.toList p] where
    pr f tl o = nested (f <+> "::") (denv, o{ overArgs = tl })

instance (IsType t, Pretty t) => Pretty (Datatypes, Overload t) where
  pretty' (_, Over _ a r _ Nothing) = 1 #> hsep (map (<+> "->") a) <+> r
  pretty' (denv, o@(Over _ _ _ v (Just e))) = sep [pretty' (denv, o{ overBody = Nothing }),
    '=' <+> (1 #> hsep (map (<+> "->") v)) <+> (denv,e)]

instance HasVar (Datatypes, Exp) where
  var v = (error "HasVar (Datatypes, Exp)", var v)
  unVar (_,e) = unVar e

instance Pretty (Datatypes, Exp) where
  pretty' (denv, ExpSpec e t) = 2 #> guard 2 (denv,e) <+> "::" <+> t
  pretty' (denv, ExpLet v e body) = 1 #>
    "let" <+> v <+> '=' <+> pretty (denv,e) <+> "in" $$ pretty (denv,body)
  pretty' (denv, ExpCase v pl d) = 1 #>
    nested ("case" <+> v <+> "of")
      (vcat (map arm pl ++ def d)) where
    arm (c, vl, e) = prettyop c vl <+> "->" <+> pretty (denv,e)
    def Nothing = []
    def (Just e) = ["_ ->" <+> pretty (denv,e)]
  pretty' (denv, ExpVal t v) = prettyval denv t v
  pretty' (_, ExpVar v) = pretty' v
  pretty' (denv, ExpApply e1 e2) = uncurry prettyop (apply e1 [(denv,e2)])
    where apply (ExpApply e a) al = apply e ((denv,a):al)
          apply e al = ((denv,e),al)
  pretty' (denv, ExpCons (V ":") [h,t]) | Just t' <- extract t = pretty' $
    brackets $ 3 #> punctuate ',' (map (\e -> pretty' (denv,e)) $ h : t') where
    extract (ExpCons (V "[]") []) = Just []
    extract (ExpCons (V ":") [h,t]) = (h :) =.< extract t
    extract _ = Nothing
  pretty' (denv, ExpCons c args) = prettyop c $ prettys denv args
  pretty' (denv, ExpPrim p el) = prettyop (V (primString p)) $ prettys denv el
  pretty' (denv, ExpBind v e1 e2) = 0 #>
    v <+> "<-" <+> (denv,e1) $$ (denv,e2)
  pretty' (denv, ExpReturn e) = prettyap "return" [pretty' (denv,e)]
  pretty' (denv, ExpLoc _ e) = pretty' (denv,e)
  --pretty' (ExpLoc l e) = "{-@" <+> show l <+> "-}" <+> pretty' e

prettys :: Datatypes -> [Exp] -> [Doc']
prettys denv = map (\e -> pretty' (denv,e))
