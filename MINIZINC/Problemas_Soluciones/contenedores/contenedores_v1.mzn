% LUIS POZAS PALOMO
% ===================================================
% "Bin Packing" con solucion array[1..n] of var 1..k
% Es decir, a cada elemento le asigno un contenedor.
% ===================================================

par int: n;
par int: k;
par int: V;
array[1..n] of par int: volume;

% SOLUCION:
% =========
array[1..n] of var 1..k: asig;

% RESTRICCIONES PROBLEMA:
% =======================

constraint forall(i in 1..k) ( (sum(j in 1..n where asig[j] = i)(volume[j])) <= V );

% BUSCO SOLUCION:
% ===============
   
% solve satisfy;

% Maximizo el espacio restante de los contenedores, lo cual
% estoy maximizando el numero de contenedores vacios.
                 
solve maximize 
max([V - (sum(j in 1..n where asig[j] = k)(volume[j])) | i in 1..k]);

% IMPRIMIR SALIDA:
% ================
output [ "\(asig[i]) " | i in 1..n ]
