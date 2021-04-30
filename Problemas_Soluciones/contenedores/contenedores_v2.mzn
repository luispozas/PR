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
array[1..n,1..k] of var 0..1: asig;

% RESTRICCIONES PROBLEMA:
% =======================

constraint forall(j in 1..k) ( (sum(i in 1..n where asig[i, j] = 1)(volume[i])) <= V );

constraint forall(i in 1..n) ( (sum(j in 1..k)(asig[i, j])) = 1 );

% BUSCO SOLUCION:
% ===============
              
%solve satisfy;

% Maximizo el espacio restante de los contenedores, lo cual
% estoy maximizando el numero de contenedores vacios.

solve maximize max([V - (sum(i in 1..n where asig[i, j] = 1)(volume[i])) | j in 1..k]);

% IMPRIMIR SALIDA:
% ================

output [ "\(asig[i,j])" ++ 
         if j == k then "\n" else " " endif |
         i in 1..n, j in 1..k
];

