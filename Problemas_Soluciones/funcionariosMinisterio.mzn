include "alldifferent.mzn";

% PARAMETROS DE ENTRADA:
% ======================

% Numero de funcionarios y trabajos
par int: N;
% Tiempos funcionarios - trabajos
array[1..N, 1..N] of par int: tiempos; 

% SOLUCION:
% =========
array[1..N] of var 1..N: asig;

% RESTRICCIONES PROBLEMA:
% =======================

% Se puede pasar una lista intensional pero retrasaria 
% la ejecucion al tener que crearla, mejor aprovechar 
% la que tenemos como solucion.
% constraint alldifferent( [ puzzle[i,j] | j in PuzzleRange ])
constraint alldifferent( asig );

solve minimize sum(i in 1..N)(tiempos[i, asig[i]]);

% SALIDA:
% =======
output [ show(sum(i in 1..N) (tiempos[i, asig[i]])) ];

