{-# LANGUAGE RecordWildCards #-}

{-|
Module      : Main
Description : Compilador de FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Main where

import System.Console.Haskeline ( defaultSettings, getInputLine, runInputT, InputT )
import Control.Monad.Catch (MonadMask)

import Control.Monad.Trans
import Data.List (nub, isPrefixOf, intercalate )
import Data.Char ( isSpace )
import Control.Exception ( catch , IOException )
import System.IO ( hPrint, stderr, hPutStrLn )
import Data.Maybe ( fromMaybe, catMaybes )
import Bytecompile (bytecompileModule, bytecompileModuleNoOpt, bcWrite, bcRead, runBC, showBC)
import Bytecompile8 (bytecompileModule8, bytecompileModuleNoOpt8, bcWrite8, bcRead8, runBC8, showBC8)

import System.Exit ( exitWith, ExitCode(ExitFailure) )
import Options.Applicative

import Global
import Errors
import Lang
import Parse ( P, tm, program, declOrTm, runP )
import Elab ( elab, elabDecl, elabType )
import Eval ( eval )
import PPrint ( pp , ppTy, ppDecl, ppSTy )
import MonadFD4
import TypeChecker ( tc, tcDecl )
import System.FilePath (dropExtension)
import Optimize (optimizeDecl)

import CEK ( runCEK )

import ClosureConvert (runCC)
import C (ir2C)

prompt :: String
prompt = "FD4> "

-- | Parser de banderas
parseMode :: Parser (Mode,Bool,Bool)
parseMode = (, ,) <$>
      (flag' Typecheck ( long "typecheck" <> short 't' <> help "Chequear tipos e imprimir el término")
      <|> flag' InteractiveCEK (long "interactiveCEK" <> short 'k' <> help "Ejecutar interactivamente en la CEK")
      <|> flag' CEK (long "cek" <> short 'l' <> help "Ejecutar en la CEK")
      <|> flag' Bytecompile (long "bytecompile" <> short 'm' <> help "Compilar a la BVM")
      <|> flag' BytecompileNoOpt (long "bytecompileNoOpt" <> short 'n' <> help "Compilar a la BVM sin Optimizaciones (sin Tailcall)")
      <|> flag' BytecompileNoOpt8 (long "bytecompileNoOpt8" <> short 'v' <> help "Compilar a la BVM 8bits sin Optimizaciones (sin Tailcall)")
      <|> flag' Bytecompile8 (long "bytecompile8" <> short 'b' <> help "Compilar a la BVM de 8 bits")
      <|> flag' RunVM (long "runVM" <> short 'r' <> help "Ejecutar bytecode en la BVM")
      <|> flag' RunVM8 (long "runVM8" <> short 'y' <> help "Ejecutar bytecode8 en la BVM de 8 bits")
      <|> flag Interactive Interactive ( long "interactive" <> short 'i' <> help "Ejecutar en forma interactiva")
      <|> flag Eval        Eval        (long "eval" <> short 'e' <> help "Evaluar programa")
      <|> flag' CC (long "cc" <> short 'c' <> help "Compilar a código C")
  -- <|> flag' Canon ( long "canon" <> short 'n' <> help "Imprimir canonicalización")
  -- <|> flag' Assembler ( long "assembler" <> short 'a' <> help "Imprimir Assembler resultante")
  -- <|> flag' Build ( long "build" <> short 'b' <> help "Compilar")
      )
   <*> flag False True (long "optimize" <> short 'o' <> help "Optimizar código")
   <*> flag False True (long "profile" <> short 'p' <> help "Muestra metricas sobre la ejecucion")

-- | Parser de opciones general, consiste de un modo y una lista de archivos a procesar
parseArgs :: Parser (Mode, Bool, Bool, [FilePath])
parseArgs = (\(a,b,c) d -> (a,b,c,d)) <$> parseMode <*> many (argument str (metavar "FILES..."))

main :: IO ()
main = execParser opts >>= go
  where
    opts = info (parseArgs <**> helper)
      ( fullDesc
     <> progDesc "Compilador de FD4"
     <> header "Compilador de FD4 de la materia Compiladores 2023" )

    go :: (Mode, Bool, Bool,[FilePath]) -> IO ()
    go (Interactive, opt, prof, files) =
              runOrFail (Conf opt prof Interactive) (runInputT defaultSettings (repl files))
    go (InteractiveCEK, opt, prof, files) =
              runOrFail (Conf opt prof InteractiveCEK) (runInputT defaultSettings (repl files))
    go (RunVM, opt, True, files) = 
              runOrFailProf (Conf opt True RunVM) $ mapM_ runVM files
    go (RunVM, opt, prof, files) =
              runOrFail (Conf opt prof RunVM) $ mapM_ runVM files
    go (RunVM8, opt, True, files) = 
              runOrFailProf (Conf opt True RunVM8) $ mapM_ runVM files
    go (RunVM8, opt, prof, files) =
              runOrFail (Conf opt prof RunVM8) $ mapM_ runVM files
    go (CEK, opt, True, files) = 
              runOrFailProf (Conf opt True CEK) $ mapM_ compileFile files
    go (m, opt, prof, files) =
              runOrFail (Conf opt prof m) $ mapM_ compileFile files

runOrFail :: Conf -> FD4 a -> IO a
runOrFail c m = do
  r <- runFD4 m c
  case r of
    Left err -> do
      liftIO $ hPrint stderr err
      exitWith (ExitFailure 1)
    Right v -> return v

runOrFailProf :: Conf -> FD4Prof a -> IO a
runOrFailProf c m = do
  r <- runFD4Prof m c
  case r of
    Left err -> do
      liftIO $ hPrint stderr err
      exitWith (ExitFailure 1)
    Right v -> return v

repl :: (MonadFD4 m, MonadMask m) => [FilePath] -> InputT m ()
repl args = do
       lift $ setInter True
       lift $ catchErrors $ mapM_ compileFile args
       s <- lift get
       when (inter s) $ liftIO $ putStrLn
         (  "Entorno interactivo para FD4.\n"
         ++ "Escriba :? para recibir ayuda.")
       loop
  where loop = do
           minput <- getInputLine prompt
           case minput of
               Nothing -> return ()
               Just "" -> loop
               Just x -> do
                       c <- liftIO $ interpretCommand x
                       b <- lift $ catchErrors $ handleCommand c
                       maybe loop (`when` loop) b

loadFile ::  MonadFD4 m => FilePath -> m [SDecl]
loadFile f = do
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStrLn stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
                         return "")
    setLastFile filename
    parseIO filename program x

compileFile ::  MonadFD4 m => FilePath -> m ()
compileFile f = do
    i <- getInter
    setInter False
    when i $ printFD4 ("Abriendo "++f++"...")
    decls <- loadFile f
    mode <- getMode
    case mode of
      Bytecompile -> do
                      declsF <- mapM handleDecl decls
                      bc <- bytecompileModule (catMaybes declsF)
                      -- printFD4 $ showBC bc 
                      liftIO $ bcWrite bc (dropExtension f ++ ".bc32")
      BytecompileNoOpt -> do
                            declsF <- mapM handleDecl decls
                            bc <- bytecompileModuleNoOpt (catMaybes declsF)
                            -- printFD4 $ showBC bc 
                            liftIO $ bcWrite bc (dropExtension f ++ ".noopt.bc32")
      Bytecompile8 -> do
                      declsF <- mapM handleDecl decls
                      bc <- bytecompileModule8 (catMaybes declsF)
                      -- printFD4 $ showBC8 bc 
                      liftIO $ bcWrite8 bc (dropExtension f ++ ".bc8")
      BytecompileNoOpt8 -> do
                            declsF <- mapM handleDecl decls
                            bc <- bytecompileModuleNoOpt8 (catMaybes declsF)
                            -- printFD4 $ showBC8 bc 
                            liftIO $ bcWrite8 bc (dropExtension f ++ ".noopt.bc8")
      CEK -> do
                mapM_ handleDecl decls
                p <- getProf
                _ <- if p then do s <- getProfStep
                                  printFD4 $ "Cantidad de pasos CEK: " ++ (show s)
                                        else return ()
                setInter i
      CC -> do
              declsF <- mapM handleDecl decls
              irs <- return (runCC (catMaybes declsF))
              ccode <- return (ir2C irs)
              --printFD4 ccode
              liftIO $ writeFile (dropExtension f ++ ".c") ccode
      Typecheck -> do 
            printFD4 ("Chequeando tipos de "++f)
            mapM_ handleDecl decls
            setInter i
      _ -> do 
            mapM_ handleDecl decls
            setInter i

runVMaux :: MonadFD4 m => FilePath -> m ()
runVMaux f = do
              m <- getMode
              case m of
                RunVM -> do
                          bc <- liftIO $ bcRead f
                          runBC bc
                RunVM8 -> do
                          bc <- liftIO $ bcRead8 f
                          runBC8 bc
                _ -> failFD4 "No deberia llegar aca"

runVM :: MonadFD4 m => FilePath -> m ()
runVM f = do
            runVMaux f
            p <- getProf
            _ <- if p then do s <- getProfStep
                              printFD4 $ "Cantidad de pasos VM: " ++ (show s)
                              ss <- getProfMaxStack
                              printFD4 $ "Tamaño maximo del stack: " ++ (show ss)
                              c <- getProfClousureCount
                              printFD4 $ "Cantidad de clausuras realizadas: " ++ (show c)
                      else return ()
            return ()


parseIO ::  MonadFD4 m => String -> P a -> String -> m a
parseIO filename p x = case runP p x filename of
                  Left e  -> throwError (ParseErr e)
                  Right r -> return r

evalDecl :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
evalDecl (Decl p x t e) = do
    e' <- eval e
    return (Decl p x t e')

runCEKDecl :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
runCEKDecl (Decl p x t e) = do 
            e' <- runCEK e
            return $ Decl p x t e'

handleDecl ::  MonadFD4 m => SDecl -> m (Maybe (Decl TTerm))
handleDecl d@(SDDecl _ _ _ _) = do
    m <- getMode
    case m of
      Typecheck -> do 
          td <- typecheckDecl d
          -- addDecl td
          opt <- getOpt
          td' <- if opt then optimizeDecl td else return td
          addDecl td'
          ppterm <- ppDecl td'
          printFD4 ppterm
          return Nothing
      Interactive -> run evalDecl d
      Eval -> run evalDecl d
      InteractiveCEK -> run runCEKDecl d
      CEK -> run runCEKDecl d
      Bytecompile -> run return d
      BytecompileNoOpt -> run return d
      Bytecompile8 -> run return d
      BytecompileNoOpt8 -> run return d
      CC -> run return d
      _ -> failFD4 "No deberia llegar aca"
    where
      typecheckDecl :: MonadFD4 m => SDecl -> m (Decl TTerm)
      typecheckDecl decl@(SDDecl _ _ _ _) = do d' <- elabDecl decl
                                               tcDecl d'
      typecheckDecl _ = failFD4 "Typecheck: No es una declaracion"
      run :: MonadFD4 m => (Decl TTerm -> m (Decl TTerm)) -> SDecl -> m(Maybe (Decl TTerm))
      run f de = do 
          td <- typecheckDecl de
          opt <- getOpt
          td' <- if opt then optimizeDecl td else return td
          ed <- f td'
          addDecl ed
          return $ Just ed

handleDecl t@(SDType _ _ _) = do 
                                m <- getMode
                                case m of
                                  Typecheck -> do 
                                      tyToGlb t
                                      ts <- ppSTy t
                                      printFD4 ts
                                      return Nothing
                                  _ -> tyToGlb t
    where
      tyToGlb :: MonadFD4 m => SDecl -> m (Maybe (Decl TTerm))
      tyToGlb (SDType _ n sty) = do ty <- elabType sty
                                    case ty of
                                        NatTy _ -> addTy (n, (NatTy (Just n)))
                                        FunTy t1 t2 _ -> addTy (n, (FunTy t1 t2 (Just n)))
                                    return Nothing
      tyToGlb _ = failFD4 "Typecheck: No es un tipo"

data Command = Compile CompileForm
             | PPrint String
             | Type String
             | Reload
             | Browse
             | Quit
             | Help
             | Noop

data CompileForm = CompileInteractive  String
                 | CompileFile         String

data InteractiveCommand = Cmd [String] String (String -> Command) String

-- | Parser simple de comando interactivos
interpretCommand :: String -> IO Command
interpretCommand x
  =  if ":" `isPrefixOf` x then
       do  let  (cmd,t')  =  break isSpace x
                t         =  dropWhile isSpace t'
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Comando desconocido `" ++ cmd ++ "'. Escriba :? para recibir ayuda.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             _   ->  do  putStrLn ("Comando ambigüo, podría ser " ++
                                   intercalate ", " ([ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                         return Noop

     else
       return (Compile (CompileInteractive x))

commands :: [InteractiveCommand]
commands
  =  [ Cmd [":browse"]      ""        (const Browse) "Ver los nombres en scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "Cargar un programa desde un archivo",
       Cmd [":print"]       "<exp>"   PPrint          "Imprime un término y sus ASTs sin evaluarlo",
       Cmd [":reload"]      ""        (const Reload)         "Vuelve a cargar el último archivo cargado",
       Cmd [":type"]        "<exp>"   Type           "Chequea el tipo de una expresión",
       Cmd [":quit",":Q"]        ""        (const Quit)   "Salir del intérprete",
       Cmd [":help",":?"]   ""        (const Help)   "Mostrar esta lista de comandos" ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs
  =  "Lista de comandos:  Cualquier comando puede ser abreviado a :c donde\n" ++
     "c es el primer caracter del nombre completo.\n\n" ++
     "<expr>                  evaluar la expresión\n" ++
     "let <var> = <expr>      definir una variable\n" ++
     unlines (map (\ (Cmd c a _ d) ->
                   let  ct = intercalate ", " (map (++ if null a then "" else " " ++ a) c)
                   in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs)

-- | 'handleCommand' interpreta un comando y devuelve un booleano
-- indicando si se debe salir del programa o no.
handleCommand ::  MonadFD4 m => Command  -> m Bool
handleCommand cmd = do
   s@GlEnv {..} <- get
   case cmd of
       Quit   ->  return False
       Noop   ->  return True
       Help   ->  printFD4 (helpTxt commands) >> return True
       Browse ->  do  printFD4 (unlines (reverse (nub (map declName glb))))
                      return True
       Compile c ->
                  do  case c of
                          CompileInteractive e -> compilePhrase e
                          CompileFile f        -> compileFile f
                      return True
       Reload ->  eraseLastFileDecls >> (getLastFile >>= compileFile) >> return True
       PPrint e   -> printPhrase e >> return True
       Type e    -> typeCheckPhrase e >> return True

compilePhrase ::  MonadFD4 m => String -> m ()
compilePhrase x = do
    dot <- parseIO "<interactive>" declOrTm x
    case dot of
      Left d  -> void $ handleDecl d
      Right t -> handleTerm t

handleTerm ::  MonadFD4 m => STerm -> m ()
handleTerm t = do
        t' <- elab t
        s <- get
        tt <- tc t' (tyEnv s)
        m <- getMode
        case m of
            InteractiveCEK -> run runCEK tt
            _ -> run eval tt
    where
      run :: MonadFD4 m => (TTerm -> m TTerm) -> TTerm -> m()
      run f t' = do 
          te <- f t'
          ppte <- pp te
          printFD4 (ppte ++ " : " ++ ppTy (getTy t'))

printPhrase   :: MonadFD4 m => String -> m ()
printPhrase x =
  do
    x' <- parseIO "<interactive>" tm x
    ex <- elab x'
    tyenv <- gets tyEnv
    tex <- tc ex tyenv
    t  <- case x' of
           (SV p f) -> fromMaybe tex <$> lookupDecl f
           _       -> return tex
    printFD4 "STerm:"
    printFD4 (show x')
    printFD4 "TTerm:"
    printFD4 (show t)

typeCheckPhrase :: MonadFD4 m => String -> m ()
typeCheckPhrase x = do
         t <- parseIO "<interactive>" tm x
         t' <- elab t
         s <- get
         tt <- tc t' (tyEnv s)
         let ty = getTy tt
         printFD4 (ppTy ty)
