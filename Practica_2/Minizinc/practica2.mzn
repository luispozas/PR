% LUIS POZAS PALOMO - PRACTICA_2 - PROGRAMACION CON RESTRICCIONES. 

%%%%%%%%%%%%%%%%%%%%%%%%%
% PARAMETROS DE ENTRADA %
%%%%%%%%%%%%%%%%%%%%%%%%%

int: meses;
int: veg;
int: anv;
int: aceites = veg+anv;

% Los precios para cada mes y tipo de aceite. (aparecen primero los VEG y luego los ANV)
array[1..meses,1..aceites] of int: precios;

% Precio producto final / tonelada.
int: VALOR;

% Maximo de aceite a refinar por tipo.
int: MAXV;  % Aceites vegetales.
int: MAXN; % Aceites no vegetales.

% Capacidad de almacenamiento de la fabrica.
int: MCAP;

% Costes de almacenamiento de cada tipo por tonelada y mes.
% Considerad que los aceites refinados no pueden ser almacenados (usar el mes que se refinan).
int: CA;

% Minima y maxima dureza
float: MinD;
float: MaxD;

% Durezas
array[1..aceites] of float: durezas;

% Cantidad de cada tipo de aceite al terminar el anio.
array[1..aceites]of int: inicio;


% Minimo beneficio
float: MinB;

% Maximo de aceites
int: K;

% Minimo de aceite a usar
int: T;

%%%%%%%%%%%%
% SOLUCION %
%%%%%%%%%%%%
array[1..meses,1..aceites] of var 0..MCAP: compra;
array[1..meses,1..aceites] of var 0..MCAP: almacen;
array[1..meses,1..aceites] of var 0..MCAP: refina;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% RESTRICCIONES PARAMETRICAS %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint assert(forall(i in 1..aceites) (MCAP >= inicio[i]), "El valor sobrante de los aceites del anio pasado excede de la capacidad de almacenamiento.");

%%%%%%%%%%%%%
% Funciones %
%%%%%%%%%%%%%

% Costes de almacenamiento mas los gastos de la compra de aceites.
function var int: calcularGastos() = sum(i in 1..meses, j in 1..aceites)(almacen[i,j]*CA + compra[i,j]*precios[i,j]);

% Toneladas de aceites refinados por el precio de venta por cada tonelada.
function var int: calcularBeneficio() = sum(i in 1..meses, j in 1..aceites)(refina[i,j]*VALOR);

% Suma ponderada por la cantidad de las durezas de cada aceite.
function var bool: comprobarDureza(var float: dureza, var int: cantidad) = (dureza >= MinD*cantidad) /\ (dureza <= MaxD*cantidad);

%%%%%%%%%%%%%%%%%
% RESTRICCIONES %
%%%%%%%%%%%%%%%%%

% Cada mes se puede refinar un maximo de aceites segun su tipo.
constraint forall(i in 1..meses) (sum(j in 1..veg) (refina[i,j]) <= MAXV);
constraint forall(i in 1..meses) (sum(j in veg+1..aceites) (refina[i,j]) <= MAXN);

% No se puede refinar mas de lo almacenado.
% Hay un limite de almacenamiento para cada tipo de aceite al inicio de cada mes.
constraint forall(i in 1..meses, j in 1..aceites) (refina[i,j] <= almacen[i,j] /\ almacen[i, j] <= MCAP);


% El primer mes el almacen contiene lo que sobro al terminar el anio anterior.
% Los siguientes meses contienen en el almacen lo que se ha comprado mas lo que habia en el almacen el mes anterior que no se ha usado para refinar.
constraint forall(j in 1..aceites)(almacen[1,j] =  compra[1,j] + inicio[j] - refina[1,j]);
constraint forall(i in 2..meses, j in 1..aceites)(almacen[i,j] = compra[i,j] + almacen[i-1,j] - refina[i,j]);


% La cantidad de cada tipo de aceite inicio = cantidad al terminar el anio.
constraint forall(i in 1..aceites)(inicio[i] = almacen[meses,i]);

% Comprobar la dureza (Si se refina entondes se suma la dureza respectiva a la cantidad refinada) 
constraint forall(i in 1..meses) (comprobarDureza(sum(j in 1..aceites)(refina[i,j]*durezas[j]),  
                                                  sum(j in 1..aceites)(refina[i,j])));
                                                  


% Minimo de beneficio que tenemos que conseguir
constraint (calcularBeneficio() - calcularGastos()) >= MinB;

% Extensiones de la practica -----------------------------------------------------------------------------------

% El producto no debe hacerse con mas de K aceites. Cada mes los aceites seleccionadas pueden cambiar.
%constraint forall(i in 1..meses)(sum(j in 1..aceites)(bool2int(refina[i,j] != 0)) <= K);

% Si un mes usamos un cierto aceite, entonces debemos usar como minimo T toneladas.
%constraint forall(i in 1..meses, j in 1..aceites)(refina[i,j] != 0 -> refina[i,j] >= T );

% Si usamos el aceite VEG 1 o el aceite VEG 2 en un cierto mes, entonces ANV 3 tambien debe ser usado ese mes.
%constraint forall(i in 1..meses)((refina[i,1] != 0 \/ refina[i,2] != 0) -> refina[i,5] != 0);


%%%%%%%%%%%%%%%%%%%%%%
% Funciones objetivo %
%%%%%%%%%%%%%%%%%%%%%%
 
%solve satisfy;
solve maximize (calcularBeneficio() - calcularGastos());
%solve minimize sum(i in 1..meses, j in 1..aceites)(refina[i,j]);


%%%%%%%%%%
% SALIDA %
%%%%%%%%%%

function var string: mes(var int: m) = 
  if(m = 1) then "Enero" else
  if(m = 2) then "Febrero" else
  if(m = 3) then "Marzo" else
  if(m = 4) then "Abril" else
  if(m = 5) then "Mayo" else
  if(m = 6) then "Junio" else
  if(m = 7) then "Julio" else
  if(m = 8) then "Agosto" else
  if(m = 9) then "Septiembre" else
  if(m = 10) then "Octubre" else
  if(m = 11) then "Noviembre" else 
  if(m = 12) then "Diciembre" else "No existe este mes"
  endif endif endif endif endif endif endif endif endif endif endif endif;
 



output [ "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n" ];
output [ "Mes \(mes(i)):\n" ++ 
         "--------------- Compra:\t\([compra[i,j] | j in 1..aceites])\n" ++ 
         "--------------- Refina:\t\([refina[i,j] | j in 1..aceites])\n" ++
         "--------------- Almacen:\t\([almacen[i,j] | j in 1..aceites])\n\n" | i in 1..meses];
output [ "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n" ];
