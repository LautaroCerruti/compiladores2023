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

elab' env (SLam p [] _) = failPosFD4 p "Elab: Funcion sin Argumentos"
elab' env (SLam p [(v,ty)] t) = do e <- elab' (v:env) t 
                                   ty' <- elabType ty 
                                   return $ Lam p v ty' (close v e)
elab' env (SLam p ((v,ty):vs) t) = do e <- elab' (v:env) (SLam p vs t) 
                                      ty' <- elabType ty 
                                      return $ Lam p v ty' (close v e)
             
elab' env (SFix p (f,fty) [] _) = failPosFD4 p "Elab: Fix sin Argumentos"
elab' env (SFix p (f,fty) [(x,xty)] t) = do e <- elab' (x:f:env) t
                                            fty' <- elabType fty 
                                            xty' <- elabType xty 
                                            return $ Fix p f fty' x xty' (close2 f x e)
   
elab' env (SFix p (f,fty) ((x,xty):xs) t) = do e <- elab' (x:f:env) (SLam p xs t)
                                               fty' <- elabType fty 
                                               xty' <- elabType xty 
                                               return $ Fix p f fty' x xty' (close2 f x e)

elab' env (SIfZ p c t e) = do c' <- elab' env c
                              t' <- elab' env t
                              e' <- elab' env e 
                              return $ IfZ p c' t' e'
-- Operadores binarios
elab' env (SBinaryOp i o t u) = do t' <- elab' env t
                                   u' <- elab' env u 
                                   return $ BinaryOp i o t' u'
-- Operador Print
elab' env (SPrint i str (Just t)) = do t' <- elab' env t
                                       return $ Print i str t' 
elab' env (SPrint i str Nothing) = return $ Lam i "x" NatTy (close "x" (Print i str (V i (Free "x"))))
-- Aplicaciones generales
elab' env (SApp p h a) = do h' <- elab' env h
                            a' <- elab' env a
                            return $ App p h' a'


elab' env (SLet p _ [] _ _) = failPosFD4 p "Elab: Let sin Argumentos" -- No deberia ocurrir
elab' env (SLet p False [(v,vty)] def body) = do d <- elab' env def
                                                 b <- elab' (v:env) body
                                                 vty' <- elabType vty
                                                 return $ Let p v vty' d (close v b)
elab' env (SLet p False ((f,fty):vs) def body) = do b <- elab' (f:env) body
                                                    d <- elab' env (SLam p vs def)
                                                    fty' <- elabType (getLetTy fty vs)
                                                    return $ Let p f fty' d (close f b)

elab' env (SLet p True [(f,fty)] def body) = failPosFD4 p "Elab: Let Rec sin Argumentos"
elab' env (SLet p True [(f,fty),(v,vty)] def body) = do b <- elab' (f:env) body
                                                        d <- elab' env (SFix p (f,fty) [(v,vty)] def)
                                                        fty' <- elabType (getLetTy fty [(v,vty)])
                                                        return $ Let p f fty' d (close f b)
elab' env (SLet p True ((f,fty):(v,vty):vs) def body) = elab' env (SLet p True [(f,(getLetTy fty vs)),(v,vty)] (SLam p vs def) body)
  
getLetTy :: STy -> [(Name,STy)] -> STy
getLetTy ty [] = ty 
getLetTy ty ((_,vty):vs) = SFunTy vty (getLetTy ty vs)

elabType :: MonadFD4 m => STy -> m Ty
elabType SNatTy = return $ NatTy 
elabType (SFunTy st st') = do t <- elabType st
                              t' <- elabType st'
                              return $ FunTy t t' 
-- elabType (STypeN name) =


elabDecl :: MonadFD4 m => SDecl -> m (Decl Term)
-- elabDecl (SDType p n st) = 
elabDecl (SDDecl p _ [] _) = failPosFD4 p "Elab: Def sin Argumentos" -- No deberia ocurrir
elabDecl (SDDecl p False [(x,xty)] t) = do t' <- elab t 
                                           xty' <- elabType xty
                                           return $ Decl p x xty' t' 
elabDecl (SDDecl p False ((f,fty):vs) t) = do t' <- elab (SLam p vs t)  
                                              fty' <- elabType (getLetTy fty vs)
                                              return $ Decl p f fty' t' 
elabDecl (SDDecl p True [(f,fty)] _) = failPosFD4 p "Elab: Def Rec sin Argumentos"
elabDecl (SDDecl p True [(f,fty),(v,vty)] t) = do t' <- elab (SFix p (f,(getLetTy fty [(v,vty)])) [(v,vty)] t) 
                                                  fty' <- elabType (getLetTy fty [(v,vty)])
                                                  return $ Decl p f fty' t' 
elabDecl (SDDecl p True ((f,fty):(v,vty):vs) t) = elabDecl (SDDecl p True [(f,(getLetTy fty vs)),(v,vty)] (SLam p vs t))  