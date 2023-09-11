-- Ej 1
En lang.hs 
Term es el ast donde se guarda solamente la posicion y el tipo de dato que pueden tomar las variables
TTerm es el ast donde se guarda la posicion y el tipo. Y tmb el tipo de dato que pueden tomar las variables

-- Ej 2
commentLine    = "#",
Creo que no se puede agregar otro caracter para agregar comentarios de 1 sola linea

commentStart :: String	
Describes the start of a block comment. Use the empty string if the language doesn't support block comments. For example "/*".

commentEnd :: String	
Describes the end of a block comment. Use the empty string if the language doesn't support block comments. For example "*/".

commentLine :: String	
Describes the start of a line comment. Use the empty string if the language doesn't support line comments. For example "//".

-- Ej 3
Trata de parsearlo como una declaracion y si falla no consume la entrada, para luego intentar parsearlo como una expr

-- Ej 4
En env llevamos la lista de nombres locales. Indica que si la variable existe dentro del env esta libre en ese termino interno, caso contrario es global.
Revisar

-- Ej 5
Las mónadas @m@ de esta clase cuentan con las operaciones:
   - @ask :: m Conf@
   - @get :: m GlEnv@
   - @put :: GlEnv -> m ()@
   - @throwError :: Error -> m a@
   - @catchError :: m a -> (Error -> m a) -> m a@
   - @liftIO :: IO a -> m a@

y otras operaciones derivadas de ellas, como por ejemplo
   - @modify :: (GlEnv -> GlEnv) -> m ()@
   - @gets :: (GlEnv -> a) -> m a@  

-- Ej 6
Es correcto en el caso de que el indice de Bruijn escape al termino que se esta abriendo, es decir que se esta trabajando en un termino que no es LC
No idea si puede ocurrir o no

-- Ej 7
module PPrint (
    pp,
    ppTy,
    ppName,
    ppDecl
    ) where

Para prityprintear nombres, termminos, declaraciones, tipos

-- Ej 8
-- | 'openAll' convierte términos locally nameless
-- a términos fully named abriendo todos las variables de ligadura que va encontrando
-- Debe tener cuidado de no abrir términos con nombres que ya fueron abiertos.
-- Estos nombres se encuentran en la lista ns (primer argumento).
Cada vez que hace un freshen para obtener un nombre nuevo lo agrega a la lista ns

-- Ej 9
Basicamente todo lo que tiene el ast
La multi es BinaryOp
Para la neg logic es agregar un nuevo al ast
Condicional lo mismo y hay que tocar mucho mas en el parser

-- Ej 10
