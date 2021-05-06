% PARAMETROS DE ENTRADA:
% ======================

% Numero canciones
par int: N;
% Tiempo ida
par int: t1;
% Tiempo vuelta
par int: t2;
% Tiempos duracion - satisfaccion
array[1..N, 1..2] of par int: dur_sat; 

% SOLUCION:
% =========
% 0 -> no reproduce
% 1 -> viaje de ida
% 2 -> viaje de vuelta

array[1..N] of var 0..2: asig;

% RESTRICCIONES PROBLEMA:
% =======================

constraint (sum(i in 1..N where asig[i] = 1)(dur_sat[i, 1])) <= t1;
constraint (sum(i in 1..N where asig[i] = 2)(dur_sat[i, 1])) <= t2;

solve maximize ((sum(i in 1..N where asig[i] = 1)(dur_sat[i, 2]))
               + 
               (sum(j in 1..N where asig[j] = 2)(dur_sat[j, 2])));

% SALIDA:
% =======
output [ show(((sum(i in 1..N where asig[i] = 1)(dur_sat[i, 2]))
               + 
               (sum(j in 1..N where asig[j] = 2)(dur_sat[j, 2])))) ];

