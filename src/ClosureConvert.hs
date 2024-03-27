module ClosureConvert (runCC) where

import Lang
import IR
import Control.Monad.State (StateT (runStateT), get, put)
import Control.Monad.Writer

import Subst ( open, open2)

freshName :: String -> StateT Int (Writer [IrDecl]) String
freshName str = do
                    i <- get
                    _ <- put $ i+1
                    return $ str ++ "" ++ show i

tyToIrTy :: Ty -> IrTy
tyToIrTy (NatTy _) = IrInt
tyToIrTy (FunTy _ _ _) = IrFunTy

fvars2Ir :: [(Name, Ty)] -> [Ir]
fvars2Ir [] = []
fvars2Ir ((n, _):xs) = (IrVar n):(fvars2Ir xs)

letify :: String -> Ir -> [(Name, Ty)] -> Ir
letify clos b l = go 1 l
                where
                    go :: Int -> [(Name, Ty)] -> Ir
                    go _ [] = b
                    go i ((n, ty):xs) = IrLet n (tyToIrTy ty) (IrAccess (IrVar clos) (tyToIrTy ty) i) (go (i+1) xs)

closureConvert :: TTerm -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V _ (Bound n)) = error "No deberia llegar aca"
closureConvert (Const _ c) = return $ IrConst c
closureConvert (V _ (Global n)) = return $ IrGlobal n
closureConvert (V _ (Free n)) = return $ IrVar n
closureConvert (BinaryOp _ bo t1 t2) = IrBinaryOp bo <$> closureConvert t1 <*> closureConvert t2
closureConvert (Print _ str t) = do 
                                    prt <- freshName ("prt")
                                    t' <- closureConvert t
                                    return $ IrLet prt IrInt (t') (IrPrint str (IrVar prt))
closureConvert (IfZ _ c t1 t2) = IrIfZ <$> closureConvert c <*> closureConvert t1 <*> closureConvert t2
closureConvert (App (_, ty) f t) = do 
                                    n <- freshName "app"
                                    f' <- closureConvert f
                                    t' <- closureConvert t
                                    return $ IrLet n IrClo f' (IrCall (IrAccess (IrVar n) IrFunTy 0) [(IrVar n), t'] (tyToIrTy ty))
closureConvert (Let _ n ty t s) = do 
                                    n' <- freshName ("let_" ++ n)
                                    t' <- closureConvert t
                                    s' <- closureConvert (open n' s)
                                    return $ IrLet n' (tyToIrTy ty) t' s'
closureConvert (Lam (_, tyf) n ty s@(Sc1 t)) = do 
                            name <- freshName "lam"
                            clos <- freshName "clos"
                            body <- closureConvert (open n s)
                            let fvars = freeVarsT t
                                codef = IrFun name (tyToIrTy tyf) [(clos, IrClo), (n, tyToIrTy ty)] (letify clos body fvars)
                            tell [codef]
                            return $ MkClosure name (fvars2Ir fvars)
closureConvert (Fix _ fn fty pn pty s@(Sc2 t)) = do
                            name <- freshName ("fix_" ++ fn)
                            param <- freshName ("param_" ++ pn)
                            clos <- freshName "clos"
                            body <- closureConvert (open2 clos param s)
                            let fvars = freeVarsT t
                                codef = IrFun name (tyToIrTy fty) [(clos, IrClo), (param, tyToIrTy pty)] (letify clos body fvars)
                            tell [codef]
                            return $ MkClosure name (fvars2Ir fvars)

convertDecl :: Decl TTerm -> StateT Int (Writer [IrDecl]) ()
convertDecl (Decl _ n ty b) = do d <- IrVal n (tyToIrTy ty) <$> closureConvert b
                                 tell [d]

runCC :: [Decl TTerm] -> IrDecls
runCC xs = let ((_, _), irs) = runWriter (runStateT (mapM convertDecl xs) 0)
           in IrDecls irs