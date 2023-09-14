{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@STerm) a locally closed (@Term@)
-}

module Elab ( elab, elabDecl) where

import Lang
import Subst
import MonadFD4

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: MonadFD4 m => STerm -> m Term
elab = elab' []

elab' :: MonadFD4 m => [Name] -> STerm -> m Term
elab' env (SV p v) =
  -- Tenemos que ver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  return $ if v `elem` env 
            then V p (Free v)
            else V p (Global v)

elab' _ (SConst p c) = return $ Const p c

elab' env (SLam p [] t) = failPosFD4 p "Elab: Funcion sin Argumentos"
elab' env (SLam p [(v,ty)] t) = do e <- elab' (v:env) t 
                                   return $ Lam p v ty (close v e)
elab' env (SLam p ((v,ty):vs) t) = do e <- elab' (v:env) (SLam p vs t) 
                                      return $ Lam p v ty (close v e)



-- WIP
elab' env (SFix p (f,fty) (x,xty) t) = Fix p f fty x xty (close2 f x (elab' (x:f:env) t))



elab' env (SIfZ p c t e) = do c' <- elab' env c
                              t' <- elab' env t
                              e' <- elab' env e 
                              return $ Ifz p c' t' e'
-- Operadores binarios
elab' env (SBinaryOp i o t u) = do t' <- elab' env t
                                   u' <= elab' env u 
                                   return $ BinaryOp i o t' u'
-- Operador Print (VER FD4)
elab' env (SPrint i str t) = do t' <= elab' env t
                                return $ Print i str t' 
-- Aplicaciones generales
elab' env (SApp p h a) = do h' <- elab' env h
                            a' <- elab' env a
                            return $ App p h' a'


-- WIP
elab' env (SLet p (v,vty) def body) =  
  Let p v vty (elab' env def) (close v (elab' (v:env) body))

elabDecl :: Decl STerm -> Decl Term
elabDecl = fmap elab
