int: numMeses;
int: tiposAceite;
%Listado de precios cada mes
array[1..numMeses,1..tiposAceite] of int: precios;
%Precio final
int: VALOR;
%Maximo de aceite a refinar por tipo
int: MAXV;
int: MAXN;
%Capacidad de alamacenamineto fabrica
int: MCAP;
%Precios de almacenamiento por mes
int: precioMes;
%Durezas
array[1..tiposAceite] of float: durezasAceite;
%Minima y maxima dureza
float: MinD;
float: MaxD;
%Cantidad al principio de aceite
int: cantidadPrincipio;
%Minimo beneficio
float: MinB;
%Maximo de aceites
int: K;
%Minimo de aceite a usar
int: T;

%Solucion
array[1..numMeses,1..tiposAceite] of var 0..MCAP: aceitesComprado;
array[1..numMeses,1..tiposAceite] of var 0..MCAP: aceiteRefinado;
array[0..numMeses,1..tiposAceite] of var 0..MCAP: aceiteAlm;

function var bool: compDureza(var float: Dureza, var float: cantidad) = Dureza >= MinD*cantidad /\ Dureza <= MaxD*cantidad;

function var int: calcGastos() = 
sum(i in 1..numMeses)(sum(j in 1..tiposAceite)(aceiteRefinado[i,j])*VALOR) -
sum(i in 1..numMeses, j in 1..tiposAceite)( aceiteAlm[i,j]*precioMes + aceitesComprado[i,j]*precios[i,j]);


constraint forall(i in 1..numMeses,j in 1..tiposAceite)(aceiteAlm[i,j] = aceitesComprado[i,j] + aceiteAlm[i-1,j] - (if i == 1 then 0 else aceiteRefinado[i-1,j] endif));

%Se empieza con una cantidad
constraint forall(i in 1..tiposAceite)(aceiteAlm[0,i] = cantidadPrincipio /\ aceiteAlm[numMeses,i] - aceiteRefinado[numMeses,i] = cantidadPrincipio);

%Maximo de refinado
constraint forall(i in 1..numMeses)(aceiteRefinado[i,1] + aceiteRefinado[i,2] <= MAXV 
/\ aceiteRefinado[i,3] + aceiteRefinado[i,4] + aceiteRefinado[i,tiposAceite] <= MAXN);

%Control de de la dureza
constraint forall(i in 1..numMeses)(compDureza(sum(j in 1..tiposAceite)(aceiteRefinado[i,j]*durezasAceite[j]),sum(j in 1..tiposAceite)(aceiteRefinado[i,j])));

%Control de ganancias, suma de gastos mas ingresos
constraint calcGastos() >= MinB;
 
 %Extensiones
constraint forall(i in 1..numMeses)(sum(j in 1..tiposAceite)(bool2int(aceiteRefinado[i,j] != 0)) <= K);

constraint forall(i in 1..numMeses, j in 1..tiposAceite)(aceiteRefinado[i,j] != 0 -> aceiteRefinado[i,j] >= T );
 
constraint forall(i in 1..numMeses)((aceiteRefinado[i,1] != 0 \/ aceiteRefinado[i,2] != 0) -> aceiteRefinado[i,5] != 0);
 
solve satisfy; 
%solve maximize calcGastos();

%output [ [ "Comprado Mes \(i): \([aceitesComprado[i,j] | j in 1..tiposAceite ])\n" | i in 1..numMeses], ["Refinado del Mes \(i): \([aceiteRefinado[i,j] | j in 1..tiposAceite ])\n" | i in 1..numMeses]];