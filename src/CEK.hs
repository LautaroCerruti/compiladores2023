module CEK where

import Lang
import MonadFD4 ( MonadFD4, lookupDecl, failFD4, printFD4 )
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

seek :: MonadFD4 m => (m ()) -> TTerm -> Env -> Kont -> m Val
seek fun val ent kont = do fun
                           seek' val ent kont
            where
                  -- seek' :: MonadFD4 m => TTerm -> Env -> Kont -> m Val
                  seek' (Print _ s t) e k = seek fun t e ((KPrint s) : k)
                  seek' (BinaryOp _ op t u) e k = seek fun t e ((KBOp e op u) : k)
                  seek' (IfZ _ c t u) e k = seek fun c e ((KIfZ e t u) : k)
                  seek' (App _ t u) e k = seek fun t e ((KArg e u) : k)
                  seek' (V _ (Global n)) e k = do                 -- ver si habria que sacarlo del primado ya que es un paso
                                              t <- lookupDecl n
                                              case t of 
                                                  Nothing -> failFD4 $ "Error de ejecución: variable no declarada: " ++ ppName n
                                                  Just v -> seek fun v e k
                  seek' (V _ (Bound i)) e k = destroy fun (e !! i) k
                  seek' (Const _ (CNat n)) e k = destroy fun (ConstN n) k
                  seek' (Lam _ x ty (Sc1 t)) e k = destroy fun (VClos (ClosFun e x ty t)) k
                  seek' (Fix _ f fty x xty (Sc2 t)) e k = destroy fun (VClos (ClosFix e f fty x xty t)) k
                  seek' (Let _ _ _ t1 (Sc1 t2)) e k = seek fun t1 e ((KLet e t2) : k)
                  seek' _ _ _ = failFD4 "No deberia pasar"

destroy :: MonadFD4 m => (m ()) -> Val -> Kont -> m Val
destroy _ v [] = return v
destroy fun val kont = do fun
                          destroy' val kont
            where
                  -- destroy' :: MonadFD4 m => Val -> Kont -> m Val 
                  destroy' v@(ConstN n) ((KPrint s) : k) = do
                                              printFD4 (s ++ show n)
                                              destroy fun v k
                  destroy' v@(ConstN n) ((KBOp e op u) : k) = seek fun u e ((KAppBOp op v) : k)
                  destroy' (ConstN n') ((KAppBOp op (ConstN n)) : k) = destroy fun (ConstN (semOp op n n')) k
                  destroy' (ConstN 0) ((KIfZ e t _) : k) = seek fun t e k
                  destroy' (ConstN _) ((KIfZ e _ t) : k) = seek fun t e k
                  destroy' (VClos c) ((KArg e t) : k) = seek fun t e ((KApp c) : k)
                  destroy' v ((KApp (ClosFun e _ _ t)) : k) = seek fun t (v : e) k
                  destroy' v ((KApp f@(ClosFix e _ _ _ _ t)) : k) = seek fun t (v : ((VClos f) : e)) k 
                  destroy' v ((KLet e t2) : k) = seek fun t2 (v : e) k
                  destroy' _ _ = failFD4 "No pasaras"

runCEK :: MonadFD4 m => (m ()) -> TTerm -> m TTerm
runCEK fun t = do 
            v <- seek fun t [] [] 
            return $ toTTerm v

toTTerm :: Val -> TTerm
toTTerm (ConstN n) = Const (NoPos, NatTy Nothing) (CNat n)  -- ver sinonimos de tipos 
toTTerm (VClos (ClosFun _ x ty t)) = Lam (NoPos, ty) x ty (Sc1 t)
toTTerm (VClos (ClosFix _ f fty x ty t)) = Fix (NoPos, ty) f fty x ty (Sc2 t)

