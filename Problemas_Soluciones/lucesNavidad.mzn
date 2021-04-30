% PARAMETROS DE ENTRADA:
% ======================
par int: tam;
par int: num_col;
par int: con_max;
array[1..num_col] of par int: consumo;

% SOLUCION:
% =========
array[1..tam] of var 1..num_col: tira;

% RESTRICCIONES PARAMETROS:
% =========================

constraint assert (tam > 1, "Tamano de la tira > 1");
constraint assert (num_col > 1, "Numero de colores > 1");
constraint assert (con_max >= 0, "Consumo maximo de la tira >= 0");
constraint assert (forall (i in 1..num_col) (consumo[i] > 0), "Consumos por tipo > 0");

% RESTRICCIONES PROBLEMA:
% =======================
% No hay mas de dos luces consecutivas del mismo color.
constraint forall(i in 1..tam-2) (not(tira[i] == tira[i+1] /\ tira[i] == tira[i+2]));

% Las tiras de luces no deben consumir mas de cierta cantidad de energia.
constraint sum(i in 1..tam) (consumo[tira[i]]) <= con_max;

% En cualquier punto de la tira la suma de las luces de un color no supere en mas de una unidad la suma de las luces de todos los demas colores.

constraint forall(i in 1..tam, j in 1..num_col)(
                      (sum(k in 1..i) (bool2int(tira[k] = j)))
                      <=
                      (sum(p in 1..i) (bool2int(tira[p] != j)))+1
              );

output [show(tira[i]-1) ++ " " | i in 1..tam];

solve satisfy;