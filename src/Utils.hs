module Utils where

import           Lang
import MonadFD4 ( MonadFD4, lookupDecl, failFD4 )

-- | Semántica de operadores binarios
semOp :: BinaryOp -> Int -> Int -> Int
semOp Add x y=  x + y
semOp Sub x y = max 0 (x - y)

usesLetInBody :: TTerm -> Bool
usesLetInBody = usesLetInBody' 0
  where
    usesLetInBody' i (V _ (Bound i2)) = i == i2
    usesLetInBody' i (BinaryOp _ _ t1 t2) = usesLetInBody' i t1 || usesLetInBody' i t2
    usesLetInBody' i (App _ t1 t2) = usesLetInBody' i t1 || usesLetInBody' i t2
    usesLetInBody' i (Lam _ _ _ (Sc1 t)) = usesLetInBody' (i+1) t
    usesLetInBody' i (Let _ _ _ t1 (Sc1 t2)) = usesLetInBody' i t1 || usesLetInBody' (i+1) t2
    usesLetInBody' i (Fix _ _ _ _ _ (Sc2 t)) = usesLetInBody' (i+2) t
    usesLetInBody' i (IfZ _ c t1 t2) = usesLetInBody' i c || usesLetInBody' i t1 || usesLetInBody' i t2
    usesLetInBody' i (Print _ _ t) = usesLetInBody' i t
    usesLetInBody' _ _ = False

treeChanged :: TTerm -> TTerm -> Bool
treeChanged (V _ _) (V _ _) = False
treeChanged (Const _ _) (Const _ _) = False
treeChanged (Lam _ _ _ (Sc1 t)) (Lam _ _ _ (Sc1 t')) = treeChanged t t'
treeChanged (Fix _ _ _ _ _ (Sc2 t)) (Fix _ _ _ _ _ (Sc2 t')) = treeChanged t t'
treeChanged (Print _ _ t) (Print _ _ t') = treeChanged t t'
treeChanged (BinaryOp _ _ t1 t2) (BinaryOp _ _ t1' t2') = treeChanged t1 t1' || treeChanged t2 t2'
treeChanged (App _ t1 t2) (App _ t1' t2') = treeChanged t1 t1' || treeChanged t2 t2'
treeChanged (Let _ _ _ t1 (Sc1 t2)) (Let _ _ _ t1' (Sc1 t2')) = treeChanged t1 t1' || treeChanged t2 t2'
treeChanged (IfZ _ c t1 t2) (IfZ _ c' t1' t2') = treeChanged c c' || treeChanged t1 t1' || treeChanged t2 t2'
treeChanged _ _ = True

termSize :: MonadFD4 m => TTerm -> m Int
termSize (V _ (Bound _)) = return 1
termSize (V _ (Free _)) = return 1
termSize (V _ (Global n)) = do 
                              lt <- lookupDecl n
                              case lt of
                                Nothing -> failFD4 "Variable no declarada"
                                Just t -> termSize t
termSize (Const _ _) = return 1
termSize (Print _ str t) = termSize t >>= \s -> return (1 + s)
termSize (IfZ _ c t1 t2) = do
                                cs <- termSize c 
                                t1s <- termSize t1 
                                t2s <- termSize t2
                                return (1 + cs + t1s + t2s)
termSize (Lam _ _ _ (Sc1 t)) = termSize t >>= \s -> return (1 + s)
termSize (App _ t u) = do
                          ts <- termSize t 
                          us <- termSize u
                          return (1 + ts + us)
termSize (Fix _ _ _ _ _ (Sc2 t)) = termSize t >>= \s -> return (1 + s)
termSize (Let _ _ _ def (Sc1 t)) = do
                                      defs <- termSize def 
                                      ts <- termSize t
                                      return (1 + defs + ts)
termSize (BinaryOp p op t1 t2) = do 
                                      t1s <- termSize t1 
                                      t2s <- termSize t2
                                      return (1 + t1s + t2s)

hasEffects :: MonadFD4 m => TTerm -> m Bool
hasEffects (V _ (Bound _)) = return False
hasEffects (V _ (Free _)) = return False
hasEffects (V _ (Global n)) = do 
                                lt <- lookupDecl n
                                case lt of
                                  Nothing -> failFD4 "Variable no declarada"
                                  Just t -> hasEffects t
hasEffects (Const _ _) = return False
hasEffects (Print _ str t) = return True
hasEffects (IfZ _ c t1 t2) = do
                                cb <- hasEffects c 
                                t1b <- hasEffects t1 
                                t2b <- hasEffects t2
                                return (cb || t1b || t2b)
hasEffects (Lam _ _ _ (Sc1 t)) = hasEffects t
hasEffects (App _ t u) = do
                          tb <- hasEffects t 
                          ub <- hasEffects u
                          return (tb || ub)
hasEffects (Fix _ _ _ _ _ (Sc2 t)) = return True  -- un posible efecto es la divergecia y no podemos saber si un fix termina o no, por lo que tomamos como que es un efecto
hasEffects (Let _ _ _ def (Sc1 t)) = do
                                        defb <- hasEffects def 
                                        tb <- hasEffects t
                                        return (defb || tb)
hasEffects (BinaryOp p op t1 t2) = do 
                                      t1b <- hasEffects t1 
                                      t2b <- hasEffects t2
                                      return (t1b || t2b)