-- Ejercicio 1

fix(fact: N -> N)(x : N).
ifz x then 1 else mul x (fact (subt x 1))

fix(exp: N -> N -> N)(x : N).
fun(y : N).
ifz y then 1 else (ifz (subt y 1) then x else mul x (exp x (subt y 1)))

fun(x : N).fun(y : N).subt x y

-- Ejercicio 2

true = fun(t : T).fun(f : T).t
false = fun(t : T).fun(f : T).f

-- Lazy
fun(p : T -> T -> T).fun(y : T).fun(x : T).p y x

-- Sol para circumvent el call by val
ifthenelse = fun(p : T -> T -> T).fun(yf: N -> T).fun(xf: N -> T).
ifz p 0 1 then yf 0 else xf 0

ifthenelse (true) (fun(n:N).y) (fun(n:N).x)

-- Tuples

pair = fun(x : T).fun(y : T).fun(b : T -> T -> T).ifthenelse b (fun(n:N).x) (fun(n:N).y)

fst = fun(p : P).p true
snd = fun(p : P).p false

-- Ejercicio 3
fix(gcd: N -> N -> N)(m : N).
fun(n : N).
ifz n then m else (ifz m then n else (ifz (subt n m) then gcd (subt m n) n else gcd m (subt n m)))

-- Ejercicio 4
fix(R : T -> (T -> N -> T) -> (N -> T))(z : T).
fun(s : T -> N -> T).fun(n : N).
ifz n then z else s (R z s (subt n 1)) n

-- Ejercicio 5
fun(f : N -> N).(fix(min : N -> N)(z : N). ifz f z then z else min (addt z 1)) 0

-- Ejercicio 6
Sean 
t2 = add n 1
t1 = fun(y : T).add x y
m = n+1

E-APP
(fun(x : T) -> t1) t2 = fun(y : T).add m y

t1[t2/x] = fun(y : T).add (add n 1) y

