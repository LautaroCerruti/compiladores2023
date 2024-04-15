{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use record patterns" #-}
{-|
Module      : PPrint
Description : Pretty printer para FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module PPrint (
    pp,
    ppTy,
    ppSTy,
    ppName,
    ppDecl
    ) where

import Lang
import Subst ( open, open2 )
import Common ( Pos )

import Data.Text ( unpack )
import Prettyprinter.Render.Terminal
  ( renderStrict, italicized, color, colorDull, Color (..), AnsiStyle )
import Prettyprinter
    ( (<+>),
      annotate,
      defaultLayoutOptions,
      layoutSmart,
      nest,
      sep,
      parens,
      emptyDoc,
      Doc,
      Pretty(pretty) )
import MonadFD4 ( gets, failFD4, MonadFD4 )
import Global ( GlEnv(glb) )
import Data.List

freshen :: [Name] -> Name -> Name
freshen ns n = let cands = n : map (\i -> n ++ show i) [0..] 
               in head (filter (`notElem` ns) cands)

toSType :: Ty -> STy 
toSType (NatTy Nothing) = SNatTy
toSType (NatTy (Just name)) = STypeN name
toSType (FunTy t t' Nothing) = SFunTy (toSType t) (toSType t')
toSType (FunTy t t' (Just name)) = STypeN name

-- | 'openAll' convierte términos locally nameless
-- a términos fully named abriendo todos las variables de ligadura que va encontrando
-- Debe tener cuidado de no abrir términos con nombres que ya fueron abiertos.
-- Estos nombres se encuentran en la lista ns (primer argumento).
openAll :: (i -> Pos) -> [Name] -> Tm i Var -> STerm
openAll gp ns (V p v) = case v of 
      Bound i ->  SV (gp p) $ "(Bound "++show i++")" --este caso no debería aparecer
                                               --si el término es localmente cerrado
      Free x -> SV (gp p) x
      Global x -> SV (gp p) x
openAll gp ns (Const p c) = SConst (gp p) c
openAll gp ns (Lam p x ty t) = 
  let x' = freshen ns x 
  in SLam (gp p) [(x',(toSType ty))] (openAll gp (x':ns) (open x' t))
openAll gp ns (App p t u) = SApp (gp p) (openAll gp ns t) (openAll gp ns u)
openAll gp ns (Fix p f fty x xty t) = 
  let 
    x' = freshen ns x
    f' = freshen (x':ns) f
  in SFix (gp p) (f',(toSType fty)) [(x',(toSType xty))] (openAll gp (x:f:ns) (open2 f' x' t))
openAll gp ns (IfZ p c t e) = SIfZ (gp p) (openAll gp ns c) (openAll gp ns t) (openAll gp ns e)
openAll gp ns (Print p str t) = SPrint (gp p) str (Just (openAll gp ns t))
openAll gp ns (BinaryOp p op t u) = SBinaryOp (gp p) op (openAll gp ns t) (openAll gp ns u)
openAll gp ns (Let p v ty m n) = 
    let v'= freshen ns v 
    in  SLet (gp p) False [(v',(toSType ty))] (openAll gp ns m) (openAll gp (v':ns) (open v' n))

--Colores
constColor :: Doc AnsiStyle -> Doc AnsiStyle
constColor = annotate (color Red)
opColor :: Doc AnsiStyle -> Doc AnsiStyle
opColor = annotate (colorDull Green)
keywordColor :: Doc AnsiStyle -> Doc AnsiStyle
keywordColor = annotate (colorDull Green) -- <> bold)
typeColor :: Doc AnsiStyle -> Doc AnsiStyle
typeColor = annotate (color Blue <> italicized)
typeOpColor :: Doc AnsiStyle -> Doc AnsiStyle
typeOpColor = annotate (colorDull Blue)
defColor :: Doc AnsiStyle -> Doc AnsiStyle
defColor = annotate (colorDull Magenta <> italicized)
nameColor :: Doc AnsiStyle -> Doc AnsiStyle
nameColor = id

-- | Pretty printer de nombres (Doc)
name2doc :: Name -> Doc AnsiStyle
name2doc n = nameColor (pretty n)

-- |  Pretty printer de nombres (String)
ppName :: Name -> String
ppName = id

-- | Pretty printer para tipos (Doc)
ty2doc :: STy -> Doc AnsiStyle
ty2doc SNatTy     = typeColor (pretty "Nat")
ty2doc (SFunTy x@(SFunTy _ _) y) = sep [parens (ty2doc x), typeOpColor (pretty "->"),ty2doc y]
ty2doc (SFunTy x y) = sep [ty2doc x, typeOpColor (pretty "->"),ty2doc y] 
ty2doc (STypeN name) = typeColor (pretty name)

-- | Pretty printer para tipos (String)
ppTy :: Ty -> String
ppTy = render . ty2doc . toSType

c2doc :: Const -> Doc AnsiStyle
c2doc (CNat n) = constColor (pretty (show n))

binary2doc :: BinaryOp -> Doc AnsiStyle
binary2doc Add = opColor (pretty "+")
binary2doc Sub = opColor (pretty "-")

collectApp :: STerm -> (STerm, [STerm])
collectApp = go [] where
  go ts (SApp _ h tt) = go (tt:ts) h
  go ts h = (h, ts)

parenIf :: Bool -> Doc a -> Doc a
parenIf True = parens
parenIf _ = id

-- t2doc at t :: Doc
-- at: debe ser un átomo
-- | Pretty printing de términos (Doc)
t2doc :: Bool     -- Debe ser un átomo? 
      -> STerm    -- término a mostrar
      -> Doc AnsiStyle
-- Uncomment to use the Show instance for STerm
{- t2doc at x = text (show x) -}
t2doc at (SV _ x) = name2doc x
t2doc at (SConst _ c) = c2doc c

t2doc at (SLam _ xs t) =
  parenIf at $
  sep [sep [ keywordColor (pretty "fun")
           , multibinding2doc xs
           , opColor(pretty "->")]
      , nest 2 (t2doc False t)]

t2doc at t@(SApp _ _ _) =
  let (h, ts) = collectApp t in
  parenIf at $
  t2doc True h <+> sep (map (t2doc True) ts)

t2doc at (SFix _ (f,fty) xs m) =
  parenIf at $
  sep [ sep [keywordColor (pretty "fix")
                  , binding2doc (f, fty)
                  , multibinding2doc xs
                  , opColor (pretty "->") ]
      , nest 2 (t2doc False m)
      ]

t2doc at (SIfZ _ c t e) =
  parenIf at $
  sep [keywordColor (pretty "ifz"), nest 2 (t2doc False c)
     , keywordColor (pretty "then"), nest 2 (t2doc False t)
     , keywordColor (pretty "else"), nest 2 (t2doc False e) ]

t2doc at (SPrint _ str (Just t)) =
  parenIf at $
  sep [keywordColor (pretty "print"), pretty (show str), t2doc True t]
t2doc at (SPrint _ str Nothing) =
  parenIf at $
  sep [keywordColor (pretty "print"), pretty (show str)]

t2doc at (SLet _ _ [] _ _) = error "let sin parametros" -- no deberia ocurrir
t2doc at (SLet _ isRec [(v,ty)] t t') =
  parenIf at $
  sep [
    sep [keywordColor (pretty "let")
       , if isRec then keywordColor (pretty "rec") else emptyDoc
       , binding2doc (v,ty)
       , opColor (pretty "=")]
  , nest 2 (t2doc False t)
  , keywordColor (pretty "in")
  , nest 2 (t2doc False t') ]
t2doc at (SLet _ isRec ((v, ty):xs) t t') =
  parenIf at $
  sep [
    sep [keywordColor (pretty "let")
       , if isRec then keywordColor (pretty "rec") else emptyDoc
       , name2doc v
       , multibinding2doc xs
       , pretty ":"
       , ty2doc ty
       , opColor (pretty "=") ]
  , nest 2 (t2doc False t)
  , keywordColor (pretty "in")
  , nest 2 (t2doc False t') ]

t2doc at (SBinaryOp _ o a b) =
  parenIf at $
  t2doc True a <+> binary2doc o <+> t2doc True b

binding2doc :: (Name, STy) -> Doc AnsiStyle
binding2doc (x, ty) =
  parens (sep [name2doc x, pretty ":", ty2doc ty])

multibinding2doc :: [(Name, STy)] -> Doc AnsiStyle
multibinding2doc xs = 
  let 
    grouped = groupBy (\a b -> snd a == snd b) xs 
    aux = map (\x -> (map fst x, snd (head x))) grouped
  in
  sep (map (\a -> parens (sep (map name2doc (fst a) ++ [pretty ":", ty2doc (snd a)]))) aux)

-- | Pretty printing de términos (String)
pp :: MonadFD4 m => TTerm -> m String
-- Uncomment to use the Show instance for Term
{- pp = show -}
pp t = do
       gdecl <- gets glb
       return (render . t2doc False $ openAll fst (map declName gdecl) t)

render :: Doc AnsiStyle -> String
render = unpack . renderStrict . layoutSmart defaultLayoutOptions

-- | Pretty printing de declaraciones
ppDecl :: MonadFD4 m => Decl TTerm -> m String
ppDecl (Decl p x ty t) = do 
  gdecl <- gets glb
  let SDDecl _ isRec sargs sterm = resugarDecl (SDDecl p False [(x, toSType ty)] (resugarT (openAll fst (filter ((/=) x) (map declName gdecl)) t))) in
    case sargs of
      [(f, fty)] -> return (render $ sep [defColor (pretty "let")
                        , if isRec then keywordColor (pretty "rec") else emptyDoc
                        , name2doc f 
                        , pretty ":"
                        , ty2doc fty
                        , defColor (pretty "=")] 
                    <+> nest 2 (t2doc False sterm))
      ((f, fty):xs) -> return (render $ sep [defColor (pretty "let")
                        , if isRec then keywordColor (pretty "rec") else emptyDoc
                        , name2doc f 
                        , multibinding2doc xs
                        , pretty ":"
                        , ty2doc fty
                        , defColor (pretty "=")] 
                    <+> nest 2 (t2doc False sterm))
      _ -> failFD4 "Decl without name"
                  
resugarT :: STerm -> STerm
-- SLam
resugarT t@(SLam il xs (SPrint i str (Just (SV _ v)))) = if v == (fst $ last xs) 
                                                          then 
                                                            case xs of 
                                                              [_] -> SPrint i str Nothing
                                                              _ -> SLam il (init xs) (SPrint i str Nothing) 
                                                          else t
resugarT (SLam i xs (SLam _ ys t)) = resugarT $ SLam i (xs ++ ys) t
resugarT (SLam i xs t) = SLam i xs (resugarT t)
-- SFix
resugarT (SFix i f xs (SLam _ ys t)) = resugarT $ SFix i f (xs ++ ys) t
resugarT (SFix i f xs t) = SFix i f xs (resugarT t)
-- SLet
resugarT (SLet i False [(f, SFunTy _ ty)] (SFix _ _ xs t1) t2) =
  resugarT $ SLet i True ((f, ty):xs) t1 t2
resugarT (SLet i b ((f, SFunTy _ ty):xs) (SLam _ ys t1) t2) = 
  resugarT $ SLet i b ((f, ty):(xs ++ ys)) t1 t2
resugarT (SLet i b xs t1 t2) = SLet i b xs (resugarT t1) (resugarT t2)
-- Others
resugarT (SApp i t1 t2) = SApp i (resugarT t1) (resugarT t2)
resugarT (SPrint i str (Just t)) = SPrint i str (Just $ resugarT t)
resugarT (SBinaryOp i bo t1 t2) = SBinaryOp i bo (resugarT t1) (resugarT t2)
resugarT (SIfZ i b t1 t2) = SIfZ i (resugarT b) (resugarT t1) (resugarT t2)
resugarT t = t

resugarDecl :: SDecl -> SDecl
resugarDecl (SDType _ _ _) = error "Declaracion de tipos no puede ser azucarada"
resugarDecl (SDDecl i b [(f, fty)] (SLam _ ys t1)) = SDDecl i b ((f, removeNTypes (length ys) fty):ys) t1
resugarDecl d@(SDDecl i False [(f, fty)] (SFix _ (fr, _) ys t1)) = if f == fr then SDDecl i True ((f, removeNTypes (length ys) fty):ys) t1 else d
resugarDecl d = d

removeNTypes :: Int -> STy -> STy
removeNTypes 0 ty = ty
removeNTypes n (SFunTy _ ty) = removeNTypes (n-1) ty
removeNTypes _ _ = error "Error de tipos"

ppSTy :: MonadFD4 m => SDecl -> m String
ppSTy (SDType p n t) = return (render $ sep [defColor (pretty "type")
                        , name2doc n
                        , defColor (pretty "=") 
                        , ty2doc t])
ppSTy _ = failFD4 "No deberia llegar aca"