import Lang
import IR

import Subst ( open, open2)

freshName :: String -> StateT Int (Writer [IrDecl]) String
freshName str = do
                    i <- get
                    _ <- put $ i+1
                    return $ str ++ "_" ++ show i

tyToIrTy :: Ty -> IrTy
tyToIrTy (NatTy _) = IrInt
tyToIrTy (FunTy _ _ _) = IrFunTy

fvars2Ir :: [(Name, Ty)] -> [Ir]
fvars2Ir [] = []
fvars2Ir ((n, _):xs) = (IrVar n):(fvars2Ir xs)

letify :: [(Name, Ty)] -> Int -> Ir -> Ir
letify _ [] _ b = b
letify clos [(n, ty):xs] i b = IrLet n (tyToIrTy ty) (IrAccess (IrVar clos) (tyToIrTy ty) i) (letify clos xs (i+1) b)

closureConvert :: Term -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V _ (Bound n)) = error "No deberia llegar aca"
closureConvert (Const _ c) = return $ IrConst c
closureConvert (V _ (Global n)) = return $ IrGlobal n
closureConvert (V _ (Free n)) = return $ IrVar n
closureConvert (BinaryOp _ bo t1 t2) = IrBinaryOp bo <$> closureConvert t1 <*> closureConvert t2
closureConvert (Print _ str t) = IrPrint str <$> closureConvert t -- Tal vez este mal
closureConvert (IfZ _ c t1 t2) = IrIfZ <$> closureConvert c <*> closureConvert t1 <*> closureConvert t2
closureConvert (App (_, ty) f t) = do 
                                    n <- freshName "app"
                                    f' <- closureConvert f
                                    t' <- closureConvert t
                                    return $ IrLet n IrClo f' (IrCall (IrAccess (IrVar n) IrFunTy 0) [(IrVar n), t'] (tyToIrTy ty))
closureConvert (Let _ n ty t s) = IrLet <$> freshName ("let_" ++ n) <*> (pure $ tyToIrTy ty) <*> closureConvert f <*> closureConvert (open n s)
closureConvert (Lam (_, tyf) n ty s@(Sc1 t)) = do 
                            name <- freshName "lam"
                            clos <- freshName "clos"
                            body <- closureConvert (open n s)
                            let fvars = freeVarsT t
                                codef = IrFun name (tyToIrTy tyf) [(clos, IrClo), (n, tyToIrTy ty)] (letify clos fvars 1 body)
                            tell [codef]
                            return $ MkClosure clos (fvars2Ir fvars)
                            


