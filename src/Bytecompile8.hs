{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-|
Module      : Bytecompile
Description : Compila a bytecode 8. Ejecuta bytecode 8.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite compilar módulos a la Macchina. También provee
una implementación de la Macchina para ejecutar el bytecode.
-}

module Bytecompile8
  (Bytecode8, runBC8, bcWrite8, bcRead8, bytecompileModule8, showBC8, bytecompileModuleNoOpt8)
 where

import Lang
import MonadFD4
import Common
import Subst (glb2freeTerm, close, shiftIndexes)
import Utils (semOp, usesLetInBody)

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word8, Binary(put, get), decode, encode, putWord8, getWord8)
import Data.Binary.Get ( isEmpty )

import Data.List (intercalate)
import Data.Char
import Data.Bits (Bits(shiftL, shiftR))

type Opcode = Word8
type Bytecode8 = [Word8]

newtype Bytecode8bits = BC { un8 :: [Word8] }

{- Esta instancia explica como codificar y decodificar Bytecode de 8 bits -}
instance Binary Bytecode8bits where
  put (BC bs) = mapM_ putWord8 bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord8
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

--función util para debugging: muestra el Bytecode8 de forma más legible.
showOps :: Bytecode8 -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:xs)       = ("CONST " ++  show (bc2int $ take 4 xs)) : showOps (drop 4 xs)
showOps (ACCESS:xs)      = ("ACCESS " ++ show (bc2int $ take 4 xs)) : showOps (drop 4 xs)
showOps (FUNCTION:xs)    = ("FUNCTION len=" ++ show (bc2int $ take 4 xs)) : showOps (drop 4 xs)
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:xs)        = ("JUMP off=" ++ show (bc2int $ take 4 xs)) : showOps (drop 4 xs)
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg,rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps rest
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (TAILCALL:xs)    = "TAILCALL" : showOps xs
showOps (CJUMP:xs)       = ("CJUMP off=" ++ show (bc2int $ take 4 xs)) : showOps (drop 4 xs)
showOps (x:xs)           = show x : showOps xs

showBC8 :: Bytecode8 -> String
showBC8 = intercalate "; " . showOps

bccNoOpt :: MonadFD4 m => TTerm -> m Bytecode8
bccNoOpt (Const _ (CNat v)) = return $ CONST : int2bc v
bccNoOpt (BinaryOp _ op t1 t2) = do 
                              b1 <- bccNoOpt t1
                              b2 <- bccNoOpt t2
                              case op of 
                                Add -> return $ b1 ++ b2 ++ [ADD]
                                Sub -> return $ b1 ++ b2 ++ [SUB]
bccNoOpt (V _ (Bound i)) = return $ ACCESS : int2bc i
bccNoOpt (App _ t1 t2) = do 
                      b1 <- bccNoOpt t1
                      b2 <- bccNoOpt t2
                      return $ b1 ++ b2 ++ [CALL]
bccNoOpt (Lam _ _ _ (Sc1 t)) = do 
                            b <- bccNoOpt t
                            return $ [FUNCTION] ++ int2bc (1 + length b) ++ b ++ [RETURN]
bccNoOpt (Let _ _ _ t1 (Sc1 t2)) = do 
                      b1 <- bccNoOpt t1
                      b2 <- bccNoOpt t2
                      return $ b1 ++ [SHIFT] ++ b2 ++ [DROP]
bccNoOpt (Fix _ _ _ _ _ (Sc2 t)) = do 
                            b <- bccNoOpt t
                            return $ [FUNCTION] ++ int2bc (1 + length b) ++ b ++ [RETURN, FIX]
bccNoOpt (IfZ _ c t1 t2) = do 
                        bc <- bccNoOpt c
                        b1 <- bccNoOpt t1
                        b2 <- bccNoOpt t2
                        return $ bc ++ [CJUMP] ++ int2bc (5 + length b1) ++ b1 ++ [JUMP] ++ int2bc (length b2) ++ b2
bccNoOpt (Print _ s t) = do
                      b <- bccNoOpt t
                      return $ b ++ [PRINT] ++ (string2bc s) ++ [NULL, PRINTN]
bccNoOpt _ = failFD4 "Error: termino desconocido"

bytecompileModuleNoOpt8 :: MonadFD4 m => Module -> m Bytecode8
bytecompileModuleNoOpt8 m = do
                        b <- bccNoOpt (letify (map gl2fr m))
                        return $ b ++ [STOP]

bcc :: MonadFD4 m => TTerm -> m Bytecode8
bcc (Const _ (CNat v)) = return $ CONST : int2bc v
bcc (BinaryOp _ op t1 t2) = do 
                              b1 <- bcc t1
                              b2 <- bcc t2
                              case op of 
                                Add -> return $ b1 ++ b2 ++ [ADD]
                                Sub -> return $ b1 ++ b2 ++ [SUB]
bcc (V _ (Bound i)) = return $ ACCESS : int2bc i
bcc (App _ t1 t2) = do 
                      b1 <- bcc t1
                      b2 <- bcc t2
                      return $ b1 ++ b2 ++ [CALL]
bcc (Lam _ _ _ (Sc1 t)) = do 
                            b <- bct t
                            return $ [FUNCTION] ++ int2bc (length b) ++ b
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
                            return $ [FUNCTION] ++ int2bc (length b) ++ b ++ [FIX]
bcc (IfZ _ c t1 t2) = do 
                        bc <- bcc c
                        b1 <- bcc t1
                        b2 <- bcc t2
                        return $ bc ++ [CJUMP] ++ int2bc (5 + length b1) ++ b1 ++ [JUMP] ++ int2bc (length b2) ++ b2
bcc (Print _ s t) = do
                      b <- bcc t
                      return $ b ++ [PRINT] ++ (string2bc s) ++ [NULL, PRINTN]
bcc _ = failFD4 "Error: termino desconocido" 

bct :: MonadFD4 m => TTerm -> m Bytecode8
bct (App _ t1 t2) = do 
                      b1 <- bcc t1
                      b2 <- bcc t2
                      return $ b1 ++ b2 ++ [TAILCALL]
bct (IfZ _ c t1 t2) = do
                        bc <- bcc c
                        b1 <- bct t1
                        b2 <- bct t2
                        return $ bc ++ [CJUMP] ++ int2bc (length b1) ++ b1 ++ b2
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

bcs :: MonadFD4 m => TTerm -> m Bytecode8
bcs (App _ t1 t2) = do 
                      b1 <- bcs t1
                      b2 <- bcc t2
                      return $ b1 ++ b2 ++ [CALL]
bcs (Lam _ _ _ (Sc1 t)) = do 
                            b <- bcs t
                            return $ [FUNCTION] ++ int2bc (1 + length b) ++ b ++ [STOP]
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
                        return $ bc ++ [CJUMP] ++ int2bc (1 + length b1) ++ b1 ++ [STOP] ++ b2
bcs t = bcc t

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode8
string2bc = map (fromIntegral . ord)

bc2string :: Bytecode8 -> String
bc2string = map (chr . fromIntegral)

int2bc :: Int -> Bytecode8
int2bc n = let n1 = n
               n2 = (shiftR n 8)
               n3 = (shiftR n2 8)
               n4 = (shiftR n3 8)
            in map fromIntegral [n1, n2, n3, n4]

bc2int :: Bytecode8 -> Int
bc2int [n1, n2, n3, n4] = let n1' = fromIntegral n1
                              n2' = (shiftL (fromIntegral n2) 8)
                              n3' = (shiftL (fromIntegral n3) 16)
                              n4' = (shiftL (fromIntegral n4) 24)
                          in n1' + n2' + n3' + n4'
bc2int _ = error "bc2int needs 4 bytes"

bytecompileModule8 :: MonadFD4 m => Module -> m Bytecode8
bytecompileModule8 m = do
                        b <- bcs (letify (map gl2fr m))
                        return $ b ++ [STOP]

letify :: Module -> TTerm
letify [] = error ""
letify [(Decl _ n ty b)] = b
letify ((Decl _ n ty b) : xs) = Let (NoPos, ty) n ty b (close n (letify xs)) 

gl2fr :: Decl TTerm -> Decl TTerm
gl2fr (Decl p n ty t) = Decl p n ty (glb2freeTerm t)

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite8 :: Bytecode8 -> FilePath -> IO ()
bcWrite8 bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

type Env = [Val]

data Val = I Int | Fun Env Bytecode8 | RA Env Bytecode8
  deriving Show

-- | Lee de un archivo y lo decodifica a bytecode
bcRead8 :: FilePath -> IO Bytecode8
bcRead8 filename = (map fromIntegral <$> un8) . decode <$> BS.readFile filename

runBC8 :: MonadFD4 m => Bytecode8 -> m ()
runBC8 bc = do 
            p <- getProf
            if p then runMacchinaProf bc [] [] id else runMacchina bc [] []

runMacchinaProf :: MonadFD4 m => Bytecode8 -> Env -> [Val] -> (Int -> Int) -> m ()
runMacchinaProf btc env stack f = do 
                                addStep
                                checkMaxStack f
                                runMacchina' btc env stack
                    where 
                          plus1 = \c -> c+1
                          minus1 = \c -> c-1
                          minus2 = \c -> c-2
                          runMacchina' (CONST : c) e s = runMacchinaProf (drop 4 c) e ((I (bc2int (take 4 c))) : s) plus1
                          runMacchina' (ADD : c) e ((I n) : (I m) : s) = runMacchinaProf c e ((I (semOp Add m n)) : s) minus1
                          runMacchina' (SUB : c) e ((I n) : (I m) : s) = runMacchinaProf c e ((I (semOp Sub m n)) : s) minus1
                          runMacchina' (ACCESS : c) e s = runMacchinaProf (drop 4 c) e ((e!!(bc2int (take 4 c))) : s) plus1
                          runMacchina' (CALL : c) e (v : (Fun ef cf) : s) = runMacchinaProf cf (v : ef) ((RA e c) : s) minus1
                          runMacchina' (FUNCTION : c) e s = addClousureCount >>= \_ -> runMacchinaProf (drop ((bc2int (take 4 c)) + 4) c) e ((Fun e (drop 4 c)) : s) plus1
                          runMacchina' (RETURN : _) _ (v : (RA e c) : s) = runMacchinaProf c e (v : s) minus1
                          runMacchina' (TAILCALL : _) _ (v : (Fun ef cf) : s) = runMacchinaProf cf (v : ef) s minus2
                          runMacchina' (SHIFT : c) e (v : s) = runMacchinaProf c (v : e) s minus1
                          runMacchina' (DROP : c) (v : e) s = runMacchinaProf c e s id
                          runMacchina' (PRINTN : c) e a@((I n) : s) = do 
                                                                        printFD4 (show n)
                                                                        runMacchinaProf c e a id
                          runMacchina' (PRINT : c) e s = let (msg,_:rest) = span (/=NULL) c
                                                        in do
                                                              printInlineFD4 $ bc2string msg
                                                              runMacchinaProf rest e s id
                          runMacchina' (CJUMP : c) e ((I z) : s) = if z == 0 then runMacchinaProf (drop 4 c) e s minus1
                                                                                  else runMacchinaProf (drop ((bc2int (take 4 c)) + 4) c) e s minus1
                          runMacchina' (JUMP : c) e s = runMacchinaProf (drop ((bc2int (take 4 c)) + 4) c) e s id
                          runMacchina' (FIX : c) e ((Fun ef cf) : s) = let efix = (Fun efix cf) : e 
                                                                        in runMacchinaProf c e ((Fun efix cf) : s) id
                          runMacchina' (STOP : _) _ _ = return ()
                          runMacchina' c e s = failFD4 $ "Makima perdio el control con " ++ (showBC8 c) ++ " y tope de la pila" ++ (show (head s))

runMacchina :: MonadFD4 m => Bytecode8 -> Env -> [Val] -> m ()
runMacchina (CONST : c) e s = runMacchina (drop 4 c) e ((I (bc2int (take 4 c))) : s) 
runMacchina (ADD : c) e ((I n) : (I m) : s) = runMacchina c e ((I (semOp Add m n)) : s)
runMacchina (SUB : c) e ((I n) : (I m) : s) = runMacchina c e ((I (semOp Sub m n)) : s)
runMacchina (ACCESS : c) e s = runMacchina (drop 4 c) e ((e!!(bc2int (take 4 c))) : s) 
runMacchina (CALL : c) e (v : (Fun ef cf) : s) = runMacchina cf (v : ef) ((RA e c) : s) 
runMacchina (FUNCTION : c) e s = runMacchina (drop ((bc2int (take 4 c)) + 4) c) e ((Fun e (drop 4 c)) : s) -- como en el pattern matching no tomamos el tamaño de la funcion al salto hay que sumarle 4
runMacchina (RETURN : _) _ (v : (RA e c) : s) = runMacchina c e (v : s) 
runMacchina (TAILCALL : _) _ (v : (Fun ef cf) : s) = runMacchina cf (v : ef) s 
runMacchina (SHIFT : c) e (v : s) = runMacchina c (v : e) s 
runMacchina (DROP : c) (v : e) s = runMacchina c e s 
runMacchina (PRINTN : c) e a@((I n) : s) = do 
                                              printFD4 (show n)
                                              runMacchina c e a 
runMacchina (PRINT : c) e s = let (msg,_:rest) = span (/=NULL) c
                              in do
                                    printInlineFD4 $ bc2string msg
                                    runMacchina rest e s 
runMacchina (CJUMP : c) e ((I z) : s) = if z == 0 then runMacchina (drop 4 c) e s 
                                                        else runMacchina (drop ((bc2int (take 4 c)) + 4) c) e s -- como en el pattern matching no tomamos el tamaño de la rama del ifz, al salto hay que sumarle 4
runMacchina (JUMP : c) e s = runMacchina (drop ((bc2int (take 4 c)) + 4) c) e s -- lo mismo que en CJUMP
runMacchina (FIX : c) e ((Fun ef cf) : s) = let efix = (Fun efix cf) : e 
                                              in runMacchina c e ((Fun efix cf) : s) 
runMacchina (STOP : _) _ _ = return ()
runMacchina c e s = failFD4 $ "Makima perdio el control con " ++ (showBC8 c)