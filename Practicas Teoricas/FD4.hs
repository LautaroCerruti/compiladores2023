-- Ejercicio 1
0 la resta es en nats

-- Ejercicio 2
let v = print "Prueba" (1 + 1)
Estado global v = 2
Se imprime en pantalla Prueba 2

v vale 2 
v + v vale 4 y no se agrega a la lista de cadenas nada

let f = fun (x:Nat) -> print "Prueba 2" (x + x)
Estado global f = fun (x:Nat) -> print "Prueba 2" (x + x)
No se imprime nada en pantalla

si se realiza una aplicacion de f se concatena a la lista de cadenas Prueba 2 (x + x) (a lo que evalue x + x)
f 1 + f 1
Prueba 2 2 Prueba 2 2
y evalua a 4

-- Ejercicio 3
"mundo!" 2 "Hola " 2
y evalua a 2


