{-|
Module      : Global
Description : Define el estado global del compilador
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}
module Global where

import Lang

data GlEnv = GlEnv {
  inter :: Bool,        --  ^ True, si estamos en modo interactivo.
                        -- Este parámetro puede cambiar durante la ejecución:
                        -- Es falso mientras se cargan archivos, pero luego puede ser verdadero.
  lfile :: String,      -- ^ Último archivo cargado.
  cantDecl :: Int,      -- ^ Cantidad de declaraciones desde la última carga
  glb :: [Decl TTerm],  -- ^ Entorno con declaraciones globales
  glbTy :: [(Name, Ty)], -- ^ Entorno con declaraciones de tipos
  profilerState :: (Int, Int, Int) -- ^ Tupla con 3 ints para los datos de profiling
                                   -- el primero corresponde con la cantidad de pasos (ya sea de la CEK o la vm)
                                   -- el segundo al tamaño maximo del stack en la vm
                                   -- el tercero a la cantidad de clausuras creadas en la vm
}

-- ^ Entorno de tipado de declaraciones globales
tyEnv :: GlEnv ->  [(Name,Ty)]
tyEnv g = map (\(Decl _ n ty b) -> (n, ty))  (glb g)

{-
 Tipo para representar las banderas disponibles en línea de comando.
-}
data Mode =
    Interactive
  | Typecheck
  | Eval
  | InteractiveCEK
  | CEK
  | Bytecompile
  | BytecompileNoOpt
  | Bytecompile8
  | BytecompileNoOpt8
  | RunVM
  | RunVM8
  | CC
  -- | Canon
  -- | Assembler
  -- | Build
data Conf = Conf {
    opt :: Bool,          --  ^ True, si estan habilitadas las optimizaciones.
    prof :: Bool,
    modo :: Mode
}

-- | Valor del estado inicial
initialEnv :: GlEnv
initialEnv = GlEnv False "" 0 [] [] (0, 0, 0)
