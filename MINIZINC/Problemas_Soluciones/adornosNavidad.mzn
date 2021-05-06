% PARAMETROS DE ENTRADA:
% ======================
par int: num_obj;
par int: presupuesto;
array[1..num_obj, 1..2] of par int: cost_sup;

% SOLUCION:
% =========
array[1..num_obj] of var 0..1: comp;

% RESTRICCIONES PROBLEMA:
% =======================

constraint (sum(i in 1..num_obj where comp[i]=1)(cost_sup[i,1])) <= presupuesto;

solve maximize (sum(i in 1..num_obj where comp[i]=1)(cost_sup[i,2]));

% SALIDA:
% =======
output [ show(sum(i in 1..num_obj where comp[i]=1) (cost_sup[i,2])) ];

