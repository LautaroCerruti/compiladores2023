import Lang
import IR

import Subst ( open, open2)

closureConvert :: Term -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V _ (Bound n)) = error "No deberia llegar aca"
closureConvert (Const _ c) = return $ IrConst c
closureConvert (V _ (Global n)) = return $ IrGlobal n
closureConvert (V _ (Free n)) = return $ IrVar n
closureConvert (BinaryOp _ bo t1 t2) = IrBinaryOp bo <$> closureConvert t1 <*> closureConvert t2
closureConvert (Print _ str t) = IrPrint str <$> closureConvert t
closureConvert (IfZ _ c t1 t2) = IrIfZ <$> closureConvert c <*> closureConvert t1 <*> closureConvert t2
