% LUIS POZAS PALOMO 

% PARAMETROS DE ENTRADA:
% ======================

% Numero de tareas
par int: T;

% Numero de tareas
par int: D;

% Limite de tiempo
par int: Lim;

% Duracion de la tareas
array[1..T] of par int: duracion; 

% Dependencias de la tareas
array[1..T, 1..T] of par 0..1: dep; 

% SOLUCION:
% =========
array[1..T] of var 1..Lim: asig;


% RESTRICCIONES PROBLEMA:
% =======================

constraint assert (forall (i in 1..T) (duracion[i] <= D), "Alguna tarea se excede del maximo de duración");

constraint forall(i in 1..T) ((asig[i] + duracion[i]) < Lim);

constraint forall(t in 1..T) ( forall(i in 1..T where dep[t, i] = 1)(asig[i]+duracion[i] <= asig[t]) );

solve minimize max(i in 1..T) (asig[i]+duracion[i]);

%solve satisfy;
