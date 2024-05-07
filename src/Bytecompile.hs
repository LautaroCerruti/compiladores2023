{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-|
Module      : Bytecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite compilar módulos a la Macchina. También provee
una implementación de la Macchina para ejecutar el bytecode.
-}
module Bytecompile
  (Bytecode, runBC, bcWrite, bcRead, bytecompileModule, showBC, bytecompileModuleNoOpt)
 where

import Lang
import MonadFD4
import Common
import Subst (glb2freeTerm, close, shiftIndexes)
import Utils (semOp, usesLetInBody)

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )

import Data.List (intercalate)
import Data.Char

type Opcode = Int
type Bytecode = [Int]

newtype Bytecode32 = BC { un32 :: [Word32] }

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord32le
                      BC xs <- go
                      return $ BC (x:xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:

   f (CALL : cs) = ...

 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.

 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern NULL     = 0
pattern RETURN   = 1
pattern CONST    = 2
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern ADD      = 6
pattern SUB      = 7
pattern CJUMP    = 8
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
pattern JUMP     = 15
pattern TAILCALL = 16

--función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:i:xs)     = ("CONST " ++  show i) : showOps xs
showOps (ACCESS:i:xs)    = ("ACCESS " ++ show i) : showOps xs
showOps (FUNCTION:i:xs)  = ("FUNCTION len=" ++ show i) : showOps xs
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:i:xs)      = ("JUMP off=" ++ show i) : showOps xs
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg,rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps rest
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (TAILCALL:xs)    = "TAILCALL" : showOps xs
showOps (CJUMP:i:xs)     = ("CJUMP off=" ++ show i) : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

bccNoOpt :: MonadFD4 m => TTerm -> m Bytecode
bccNoOpt (Const _ (CNat v)) = return [CONST, v]
bccNoOpt (BinaryOp _ op t1 t2) = do 
                              b1 <- bccNoOpt t1
                              b2 <- bccNoOpt t2
                              case op of 
                                Add -> return $ b1 ++ b2 ++ [ADD]
                                Sub -> return $ b1 ++ b2 ++ [SUB]
bccNoOpt (V _ (Bound i)) = return [ACCESS, i]
bccNoOpt (App _ t1 t2) = do 
                      b1 <- bccNoOpt t1
                      b2 <- bccNoOpt t2
                      return $ b1 ++ b2 ++ [CALL]
bccNoOpt (Lam _ _ _ (Sc1 t)) = do 
                            b <- bccNoOpt t
                            return $ [FUNCTION, 1 + length b] ++ b ++ [RETURN]
bccNoOpt (Let _ _ _ t1 (Sc1 t2)) = do 
                      b1 <- bccNoOpt t1
                      b2 <- bccNoOpt t2
                      return $ b1 ++ [SHIFT] ++ b2 ++ [DROP]
bccNoOpt (Fix _ _ _ _ _ (Sc2 t)) = do 
                            b <- bccNoOpt t
                            return $ [FUNCTION, 1 + length b] ++ b ++ [RETURN, FIX]
bccNoOpt (IfZ _ c t1 t2) = do 
                        bc <- bccNoOpt c
                        b1 <- bccNoOpt t1
                        b2 <- bccNoOpt t2
                        return $ bc ++ [CJUMP, 2 + length b1] ++ b1 ++ [JUMP, length b2] ++ b2
bccNoOpt (Print _ s t) = do
                      b <- bccNoOpt t
                      return $ b ++ [PRINT] ++ (string2bc s) ++ [NULL, PRINTN]
bccNoOpt _ = failFD4 "Error: termino desconocido"

bytecompileModuleNoOpt :: MonadFD4 m => Module -> m Bytecode
bytecompileModuleNoOpt m = do
                        b <- bccNoOpt (letify (map gl2fr m))
                        return $ b ++ [STOP]

bcc :: MonadFD4 m => TTerm -> m Bytecode
bcc (Const _ (CNat v)) = return [CONST, v]
bcc (BinaryOp _ op t1 t2) = do 
                              b1 <- bcc t1
                              b2 <- bcc t2
                              case op of 
                                Add -> return $ b1 ++ b2 ++ [ADD]
                                Sub -> return $ b1 ++ b2 ++ [SUB]
bcc (V _ (Bound i)) = return [ACCESS, i]
bcc (App _ t1 t2) = do 
                      b1 <- bcc t1
                      b2 <- bcc t2
                      return $ b1 ++ b2 ++ [CALL]
bcc (Lam _ _ _ (Sc1 t)) = do 
                            b <- bct t
                            return $ [FUNCTION, length b] ++ b
bcc (Let _ _ _ t1 (Sc1 t2)) 
  | usesLetInBody t2 = do 
                        b1 <- bcc t1
                        b2 <- bcc t2
                        return $ b1 ++ [SHIFT] ++ b2 ++ [DROP]
  | otherwise = do 
                  b1 <- bcc t1
                  b2 <- bcc (shiftIndexes t2)
                  return $ b1 ++ [SHIFT, DROP] ++ b2
bcc (Fix _ _ _ _ _ (Sc2 t)) = do 
                            b <- bct t
                            return $ [FUNCTION, length b] ++ b ++ [FIX]
bcc (IfZ _ c t1 t2) = do 
                        bc <- bcc c
                        b1 <- bcc t1
                        b2 <- bcc t2
                        return $ bc ++ [CJUMP, 2 + length b1] ++ b1 ++ [JUMP, length b2] ++ b2
bcc (Print _ s t) = do
                      b <- bcc t
                      return $ b ++ [PRINT] ++ (string2bc s) ++ [NULL, PRINTN]
bcc _ = failFD4 "Error: termino desconocido" 

bct :: MonadFD4 m => TTerm -> m Bytecode
bct (App _ t1 t2) = do 
                      b1 <- bcc t1
                      b2 <- bcc t2
                      return $ b1 ++ b2 ++ [TAILCALL]
bct (IfZ _ c t1 t2) = do
                        bc <- bcc c
                        b1 <- bct t1
                        b2 <- bct t2
                        return $ bc ++ [CJUMP, length b1] ++ b1 ++ b2
bct (Let _ _ _ t1 (Sc1 t2))  
  | usesLetInBody t2 = do 
                        b1 <- bcc t1
                        b2 <- bct t2
                        return $ b1 ++ [SHIFT] ++ b2
  | otherwise = do 
                  b1 <- bcc t1
                  b2 <- bct (shiftIndexes t2)
                  return $ b1 ++ [SHIFT, DROP] ++ b2
bct t = do bc <- bcc t
           return $ bc ++ [RETURN]

bcs :: MonadFD4 m => TTerm -> m Bytecode
bcs (Let _ _ _ t1 (Sc1 t2)) 
  | usesLetInBody t2 = do 
                        b1 <- bcc t1
                        b2 <- bcs t2
                        return $ b1 ++ [SHIFT] ++ b2
  | otherwise = do 
                  b1 <- bcc t1
                  b2 <- bcs (shiftIndexes t2)
                  return $ b1 ++ [SHIFT, DROP] ++ b2
bcs (IfZ _ c t1 t2) = do
                        bc <- bcc c
                        b1 <- bcs t1
                        b2 <- bcs t2
                        return $ bc ++ [CJUMP, 1 + length b1] ++ b1 ++ [STOP] ++ b2
bcs t = bcc t

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode
string2bc = map ord

bc2string :: Bytecode -> String
bc2string = map chr

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule m = do
                        b <- bcs (letify (map gl2fr m))
                        return $ b ++ [STOP]

letify :: Module -> TTerm
letify [] = error ""
letify [(Decl _ n ty b)] = b
letify ((Decl _ n ty b) : xs) = Let (NoPos, ty) n ty b (close n (letify xs)) 

gl2fr :: Decl TTerm -> Decl TTerm
gl2fr (Decl p n ty t) = Decl p n ty (glb2freeTerm t)

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

type Env = [Val]

data Val = I Int | Fun Env Bytecode | RA Env Bytecode
  deriving Show

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (map fromIntegral <$> un32) . decode <$> BS.readFile filename

runBC :: MonadFD4 m => Bytecode -> m ()
runBC bc = runMacchina bc [] [] id

runMacchina :: MonadFD4 m => Bytecode -> Env -> [Val] -> (Int -> Int) -> m ()
runMacchina btc env stack f = do 
                                addStep
                                checkMaxStack f
                                runMacchina' btc env stack
                    where 
                          plus1 = \c -> c+1
                          minus1 = \c -> c-1
                          minus2 = \c -> c-2
                          runMacchina' (CONST : n : c) e s = runMacchina c e ((I n) : s) plus1
                          runMacchina' (ADD : c) e ((I n) : (I m) : s) = runMacchina c e ((I (semOp Add m n)) : s) minus1
                          runMacchina' (SUB : c) e ((I n) : (I m) : s) = runMacchina c e ((I (semOp Sub m n)) : s) minus1
                          runMacchina' (ACCESS : i : c) e s = runMacchina c e ((e!!i) : s) plus1
                          runMacchina' (CALL : c) e (v : (Fun ef cf) : s) = runMacchina cf (v : ef) ((RA e c) : s) minus1
                          runMacchina' (FUNCTION : l : c) e s = addClousureCount >>= \_ -> runMacchina (drop l c) e ((Fun e c) : s) plus1
                          runMacchina' (RETURN : _) _ (v : (RA e c) : s) = runMacchina c e (v : s) minus1
                          runMacchina' (TAILCALL : _) _ (v : (Fun ef cf) : s) = runMacchina cf (v : ef) s minus2
                          runMacchina' (SHIFT : c) e (v : s) = runMacchina c (v : e) s minus1
                          runMacchina' (DROP : c) (v : e) s = runMacchina c e s id
                          runMacchina' (PRINTN : c) e a@((I n) : s) = do 
                                                                        printFD4 (show n)
                                                                        runMacchina c e a id
                          runMacchina' (PRINT : c) e s = let (msg,_:rest) = span (/=NULL) c
                                                        in do
                                                              printInlineFD4 $ bc2string msg
                                                              runMacchina rest e s id
                          runMacchina' (CJUMP : l1 : c) e ((I z) : s) = if z == 0 then runMacchina c e s minus1
                                                                                  else runMacchina (drop l1 c) e s minus1
                          runMacchina' (JUMP : l : c) e s = runMacchina (drop l c) e s id
                          runMacchina' (FIX : c) e ((Fun ef cf) : s) = let efix = (Fun efix cf) : e 
                                                                        in runMacchina c e ((Fun efix cf) : s) id
                          runMacchina' (STOP : _) _ _ = return ()
                          runMacchina' c e s = failFD4 $ "Makima perdio el control con " ++ (showBC c)