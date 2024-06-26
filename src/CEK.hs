module CEK where

import Lang
import MonadFD4 ( MonadFD4, lookupDecl, failFD4, printFD4, addStep, getProf )
import PPrint ( ppName )
import Utils (semOp)
import Common

data Val = ConstN Int | VClos Clos
data Clos = ClosFun Env Name Ty TTerm | ClosFix Env Name Ty Name Ty TTerm

type Env = [Val]

data Frame = 
      KArg Env TTerm 
    | KApp Clos
    | KIfZ Env TTerm TTerm
    | KBOp Env BinaryOp TTerm
    | KAppBOp BinaryOp Val
    | KPrint String 
    | KLet Env TTerm

type Kont = [Frame]

seekProf :: MonadFD4 m => TTerm -> Env -> Kont -> m Val
seekProf val ent kont = do addStep
                           seek' val ent kont
            where
                  seek' :: MonadFD4 m => TTerm -> Env -> Kont -> m Val
                  seek' (Print _ s t) e k = seekProf t e ((KPrint s) : k)
                  seek' (BinaryOp _ op t u) e k = seekProf t e ((KBOp e op u) : k)
                  seek' (IfZ _ c t u) e k = seekProf c e ((KIfZ e t u) : k)
                  seek' (App _ t u) e k = seekProf t e ((KArg e u) : k)
                  seek' (V _ (Global n)) e k = do                 -- ver si habria que sacarlo del primado ya que es un paso
                                              t <- lookupDecl n
                                              case t of 
                                                  Nothing -> failFD4 $ "Error de ejecución: variable no declarada: " ++ ppName n
                                                  Just v -> seekProf v e k
                  seek' (V _ (Bound i)) e k = destroyProf (e !! i) k
                  seek' (Const _ (CNat n)) e k = destroyProf (ConstN n) k
                  seek' (Lam _ x ty (Sc1 t)) e k = destroyProf (VClos (ClosFun e x ty t)) k
                  seek' (Fix _ f fty x xty (Sc2 t)) e k = destroyProf (VClos (ClosFix e f fty x xty t)) k
                  seek' (Let _ _ _ t1 (Sc1 t2)) e k = seekProf t1 e ((KLet e t2) : k)
                  seek' _ _ _ = failFD4 "No deberia pasar"

destroyProf :: MonadFD4 m => Val -> Kont -> m Val
destroyProf v [] = return v
destroyProf val kont = do addStep
                          destroy' val kont
            where
                  destroy' :: MonadFD4 m => Val -> Kont -> m Val 
                  destroy' v@(ConstN n) ((KPrint s) : k) = do
                                              printFD4 (s ++ show n)
                                              destroyProf v k
                  destroy' v@(ConstN n) ((KBOp e op u) : k) = seekProf u e ((KAppBOp op v) : k)
                  destroy' (ConstN n') ((KAppBOp op (ConstN n)) : k) = destroyProf (ConstN (semOp op n n')) k
                  destroy' (ConstN 0) ((KIfZ e t _) : k) = seekProf t e k
                  destroy' (ConstN _) ((KIfZ e _ t) : k) = seekProf t e k
                  destroy' (VClos c) ((KArg e t) : k) = seekProf t e ((KApp c) : k)
                  destroy' v ((KApp (ClosFun e _ _ t)) : k) = seekProf t (v : e) k
                  destroy' v ((KApp f@(ClosFix e _ _ _ _ t)) : k) = seekProf t (v : ((VClos f) : e)) k 
                  destroy' v ((KLet e t2) : k) = seekProf t2 (v : e) k
                  destroy' _ _ = failFD4 "No pasaras"

seek :: MonadFD4 m => TTerm -> Env -> Kont -> m Val
seek (Print _ s t) e k = seek t e ((KPrint s) : k)
seek (BinaryOp _ op t u) e k = seek t e ((KBOp e op u) : k)
seek (IfZ _ c t u) e k = seek c e ((KIfZ e t u) : k)
seek (App _ t u) e k = seek t e ((KArg e u) : k)
seek (V _ (Global n)) e k = do 
                              t <- lookupDecl n
                              case t of 
                                    Nothing -> failFD4 $ "Error de ejecución: variable no declarada: " ++ ppName n
                                    Just v -> seek v e k
seek (V _ (Bound i)) e k = destroy (e !! i) k
seek (Const _ (CNat n)) e k = destroy (ConstN n) k
seek (Lam _ x ty (Sc1 t)) e k = destroy (VClos (ClosFun e x ty t)) k
seek (Fix _ f fty x xty (Sc2 t)) e k = destroy (VClos (ClosFix e f fty x xty t)) k
seek (Let _ _ _ t1 (Sc1 t2)) e k = seek t1 e ((KLet e t2) : k)
seek _ _ _ = failFD4 "No deberia pasar"

destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v [] = return v
destroy v@(ConstN n) ((KPrint s) : k) = do
                              printFD4 (s ++ show n)
                              destroy v k
destroy v@(ConstN n) ((KBOp e op u) : k) = seek u e ((KAppBOp op v) : k)
destroy (ConstN n') ((KAppBOp op (ConstN n)) : k) = destroy (ConstN (semOp op n n')) k
destroy (ConstN 0) ((KIfZ e t _) : k) = seek t e k
destroy (ConstN _) ((KIfZ e _ t) : k) = seek t e k
destroy (VClos c) ((KArg e t) : k) = seek t e ((KApp c) : k)
destroy v ((KApp (ClosFun e _ _ t)) : k) = seek t (v : e) k
destroy v ((KApp f@(ClosFix e _ _ _ _ t)) : k) = seek t (v : ((VClos f) : e)) k 
destroy v ((KLet e t2) : k) = seek t2 (v : e) k
destroy _ _ = failFD4 "No pasaras"

runCEK :: MonadFD4 m => TTerm -> m TTerm
runCEK t = do 
            p <- getProf
            v <- if p then seekProf t [] [] else seek t [] []
            return $ toTTerm v

toTTerm :: Val -> TTerm
toTTerm (ConstN n) = Const (NoPos, NatTy Nothing) (CNat n)
toTTerm (VClos (ClosFun _ x ty t)) = Lam (NoPos, ty) x ty (Sc1 t)
toTTerm (VClos (ClosFix _ f fty x ty t)) = Fix (NoPos, ty) f fty x ty (Sc2 t)
