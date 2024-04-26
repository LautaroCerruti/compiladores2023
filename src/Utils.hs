module Utils where

import           Lang

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