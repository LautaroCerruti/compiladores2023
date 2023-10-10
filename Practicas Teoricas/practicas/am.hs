-- Ej 1
Regla computa

let x = v1 in t2 -> [v1/x]t2

Regla congruencia

t1 -> t1'
----------------------------
let x = t1 in t2 -> let x = t1' in t2

-- Ej 2
let x = E in t

-- Ej 3
let x = [] in t

-- Ej 4
<let x = t1 in t2, k> -> <t1, let x = [] in t2 > k>
<<v1, let x = [] in t2 > k>> -> <[v1/x]t2, k>

-- Ej 5
p . let x = [] in t
Cambia que tenemos que recordr el entorno que habia antes de evaluar el valor de x, 
ya que ese es el que entorno que le corresponde a t

-- Ej 6
<let x = t1 in t2, p, k> -> <t1, p, p. let x = [] in t2 > k>
<<v1, p. let x = [] in t2 > k>> -> <t2, p(x |-> v1), k>