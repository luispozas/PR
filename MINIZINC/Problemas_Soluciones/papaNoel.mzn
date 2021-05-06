% PARAMETROS DE ENTRADA:
% ======================
% M juguetes diferentes > 0
% N ninos > 0
% S minima satisfaccion > 0
% Unidades de cada juguetes x tipo
% Tipos juguetes
% Satisfaccion por ninos para cada juguete

par int: m;
par int: n;
par int: s;
array[1..m] of par int: disp;
enum Tipo;
array [1..m] of par Tipo: jtipo;
array [1..n, 1..m] of par int: jsat;

% DEFINIR SOLUCION:
% =================

array[1..n,1..2] of var int: sol;

% RESTRICCIONES:
% ==============
% Parseo los datos de entrada como se especifican.
% ------------------------------------------------
constraint assert (m > 0, "El #juguetes > 0");
constraint assert (n > 0, "El #ninos > 0");
constraint assert (s > 0, "El #satisfaccion > 0");

constraint assert (forall (i in 1..m) (disp[i] >= 0), "Las unidades de cada tipo >= 0");

% Especifico las restricciones del problema.
% ------------------------------------------
% La asignacion no supere la disponibilidad:
constraint forall (i in 1..m) ((sum (j in 1..n, k in 1..2)(bool2int(sol[j,k] = i))) <= disp[i]);

% Satisfaccion minima:
constraint forall (j in 1..n) ((sum (k in 1..2) (jsat[j,sol[j,k]])) >= s);

% Dos juguetes del mismo tipo a cada nino:
constraint forall (j in 1..n) (jtipo[sol[j,1]] != jtipo[sol[j,2]]);

% Eliminar redundancia en soluciones.
% (Pongo < para evitar asignar 2 iguales y salgan en orden.)
constraint forall (i in 1..n) (sol[i,1] < sol[i,2] ); 

solve satisfy;

