% LUIS POZAS PALOMO - PRACTICA_1 - PROGRAMACION CON RESTRICCIONES.

include "globals.mzn"; 

%%%%%%%%%%%%%%%%%%%%%%%%%
% PARAMETROS DE ENTRADA %
%%%%%%%%%%%%%%%%%%%%%%%%%

% Numero de dias.
par int: D;
% Numero de trabajadores.
par int: T;
% Numero de trabajadores en cada turno.
par int: N1;
par int: N2;
par int: N3;

% Numero maximo dias consecutivos.
par int: MaxDT;
% Numero maximo dias libres.
par int: MaxDL;
% Numero minimo dias trabajados.
par int: MinDT;

% Trabajadores afines.
array[1..T] of set of 1..T: afin;
par int: A;

% Categorias de los trabajadores.
par int: C;
array[1..T] of 1..C: categ;

% Dias consecutivos sin trabajar por cada trabajador.
array[1..T] of 0..D: diasLibres;

% Turno odiado por cada trabajador para cada día.
% 0 -> ninguno | 1 -> Turno1 | 2 -> Turno2 | 3 -> Turno3
array[1..T, 1..D] of 0..3: turnoLibre;

%%%%%%%%%%%%
% SOLUCION %
%%%%%%%%%%%%

% 0 -> libre | 1 -> Turno1 | 2 -> Turno2 | 3 -> Turno3
array[1..T, 1..D] of var 0..3: asig;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% RESTRICCIONES PARAMETRICAS %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint assert (D > 0, "Numero de dias a planificar > 0");
constraint assert (T > 0, "Numero de trabajadores > 0");
constraint assert (C > 0, "Numero de categorias > 0");
constraint assert (A >= 0, "Numero de trabajadores afines no puede ser negativo");
constraint assert ((N1+N2+N3) <= T , "Trabajadores insuficientes para cubrir los turnos");
constraint assert (N1 > 0 /\ N2 > 0 /\ N3 > 0 , "Hay algun turno sin trabajadores asignados");
constraint assert (MaxDT > 0, "MaxDT > 0");
constraint assert (D-(MaxDT-1) > 0, "Se exceden los dias trabajados consecutivos de los planificados");
constraint assert (MaxDL > 0, "MaxDL > 0");
constraint assert (D-(MaxDL-1) > 0, "Se exceden los dias libres consecutivos de los planificados");
constraint assert (MinDT < D /\ MinDT >= 0, "MinDT < D y MinDT > 0");
%constraint assert (forall(t in 1..T)( (MinDT - diasLibres[t])>=0 /\ diasLibres[t]>=0 ), "Los dias libres que piden los trabajadores deben ser mayor que 0");


%%%%%%%%%%%%%%%%%
% RESTRICCIONES %
%%%%%%%%%%%%%%%%%

% 1. Cada turno tiene el numero de trabajadores (N1, N2 o N3) que le corresponde:

constraint forall(d in 1..D) ( sum(t in 1..T)(bool2int(asig[t, d] = 1)) = N1 /\
                               sum(t in 1..T)(bool2int(asig[t, d] = 2)) = N2 /\
                               sum(t in 1..T)(bool2int(asig[t, d] = 3)) = N3
                             );

% 2. Un trabajador solo puede estar en un turno cada día:
% La solucion del problema no permite asignar mas de un turno a cada trabajador.

% 3. Dado un número MaxDT, garantizar que nadie trabaja MaxDT días consecutivos.

constraint forall(t in 1..T, d in 1..(D-(MaxDT-1))) 
  ((sum(k in d..(d+(MaxDT-1)))(bool2int(asig[t,k] != 0))) < MaxDT);

% 4. Dado un número MaxDL, garantizar que nadie tiene MaxDL días libres consecutivos.

constraint forall(t in 1..T, d in 1..(D-(MaxDL-1)) where diasLibres[t] = 0) 
  ((sum(k in d..(d+(MaxDL-1)))(bool2int(asig[t,k] = 0))) < MaxDL);


% 5. Dado un número MinDT, garantizar que todos trabajan como mínimo MinDT en los D días.

constraint forall(t in 1..T) 
  ((sum(d in 1..D) (bool2int(asig[t, d] != 0))) >= (MinDT - diasLibres[t]));

% 6. Un trabajador no puede hacer el último turno de un día y el primero del día siguiente
% dos veces seguidas en cuatro días consecutivos.

constraint forall(t in 1..T, d in 1..D-3)
  (if(asig[t, d] = 3) then asig[t, d+1] != 1 /\ if(asig[t, d+2] = 3) then asig[t, d+3] != 1 endif endif);

% 7. Dada una serie de parejas de trabajadores afines y un número A, cada trabajador de
% un turno tiene que estar con al menos A trabajadores afines en ese turno.

constraint if(N1 > 1 /\ N2 > 1 /\ N3 > 1) then (forall(d in 1..D)( minAfines([ asig[t,d] | t in 1..T ]))) endif;
                            
predicate minAfines(array[int] of var int:ts) = 
  forall(t in 1..T where ts[t] != 0) (
    (sum(a in afin[t] where ts[a] != 0 /\ a != t)(bool2int(ts[a] = ts[t]))) >= A
  );       

% 8. Sea C el número de categorías. Dada la categoría de los trabajadores. En cada turno
% debe haber al menos un trabajador de cada categoría. Podéis generalizar esta restricción
% a que se indique exactamente (o como mínimo) cuántos de cada categoría tiene que tener
% cada turno y tenerlo distinto para cada uno de los tres turnos.

constraint if(C > 1 /\ N1>1 /\ N2>1 /\ N3>1) then forall(d in 1..D)( minCategoria([ asig[t,d] | t in 1..T ]) ) endif;

predicate minCategoria(array[int] of var int:ts) = 
  forall(tipo in 1..3) (
    card( array_union([ { categ[t]*bool2int(ts[t] = tipo) } | t in 1..T ]) diff {0} ) >= C
  );
                          

%%%%%%%%%%%%%%%%%%%%%%
% Funciones objetivo %
%%%%%%%%%%%%%%%%%%%%%%

%====================================================================================================================================

% Anadid la posibilidad de que los trabajadores pidan dias que no quieren trabajar.
% Tened en cuenta que estos dias no cuentan en la restriccion de dias consecutivos libres
% y que hay que descontarlos de MinDT. Convertid el problema en un problema de
% optimizacion, minimizando el numero de veces que hacemos trabajar a alguien cuando
% no quiere. Pensad en formas de conseguir que los incumplimientos se distribuyan entre
% todos.

% Restriccion para plantear este objetivo:
constraint forall(t in 1..T where diasLibres[t] != 0 ) (exists (d in 1..(D - (diasLibres[t]-1))) 
  ((sum(k in d..(d + (diasLibres[t]-1)))(bool2int(asig[t,k] = 0))) = diasLibres[t]));

% El problema de minimizacion se tranforma en uno de maximizacion siempre y cuando maximicemos
% el numero de trabajadores que consiguen sus dias libres consecutivos que han pedido.
  
%solve maximize sum(t in 1..T where diasLibres[t] != 0 ) 
%  (bool2int((exists (d in 1..(D - (diasLibres[t]-1))) 
%          ((sum(k in d..(d + (diasLibres[t]-1)))(bool2int(asig[t,k] = 0))) = diasLibres[t])) ));
  
%====================================================================================================================================

% Anadid la posibilidad de que los trabajadores pidan que turno no quieren (para cada dia),
% si es que tienen alguna preferencia. Convertid el problema en un problema de optimizacion, 
% minimizando el numero de veces que incumplimos la peticion. Pensad en formas de conseguir 
% que los incumplimientos se distribuyan entre todos.

% Restriccion para plantear este objetivo:
% constraint forall(t in 1..T, d in 1..D where turnoLibre[t, d] != 0 )(asig[t, d] != turnoLibre[t, d]);

% El problema de minimizacion se tranforma en uno de maximizacion siempre y cuando maximicemos
% el numero de trabajadores que consiguen sus turnos libres que han pedido.

% Busco satisfacer completamente a cada trabajador.
%solve maximize sum(t in 1..T) (bool2int(forall(d in 1..D where turnoLibre[t, d] != 0 )(asig[t, d] != turnoLibre[t, d])));

% Busco encontrar la felicidad entre los trabajadores, voy asignando por dias.
%solve maximize sum(t in 1..T, d in 1..D where turnoLibre[t, d] != 0 )(bool2int(asig[t, d] != turnoLibre[t, d]));

%====================================================================================================================================

 solve satisfy;

%====================================================================================================================================


%%%%%%%%%%
% SALIDA %
%%%%%%%%%%

output [ "\(asig[i, j]) " ++
         if j == D then "\n" else "" endif  
         | i in 1..T, j in 1..D
];
