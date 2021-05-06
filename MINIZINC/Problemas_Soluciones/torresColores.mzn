% Data file
% tam = 10;
% data = [3, 5, 3];

% Parameters of model:
par int: tam;
enum Colores = {Blue,Red,Green};
array[Colores] of int: data;

%================================================
% Tambien se puede parametrizar enum Colores;
% para que puedan ser de todo tipo.
%================================================

% Define solution (torre) with size "tam":
array[0..tam-1] of var Colores: torre;

% Condition: two piezes minimum.
%constraint assert(tam >= 2,"Invalid datafile: " ++
    %              "Amount of tam should be more than two");

% Condicion: use the given pieces.
constraint ((sum(i in 0..tam-1)(bool2int(torre[i] = Blue))) <= (data[Blue]));
constraint ((sum(i in 0..tam-1)(bool2int(torre[i] = Red))) <= (data[Red]));
constraint ((sum(i in 0..tam-1)(bool2int(torre[i] = Green))) <= (data[Green]));

% Misma condicion que la anterior:
%constraint forall (c in Colores) (sum (i in 0..tam-1) (bool2int(torre[i]=c) ) <= data[c]);

% Condition: two green together.
constraint forall (i in 0..tam-2) 
          ((torre[i] = Green) -> (torre[i+1] != Green));
           
% Condition: #blue >= #green at all times.
constraint forall(i in 1..tam-1) (
           (sum (j in 0..i) (bool2int(torre[j] = Blue)))
           >= 
           (sum (j in 0..i) (bool2int(torre[j] = Green)))
           );
           
% Condition: The red pieze at the base.
constraint torre[0] = Red;

% Condition: #red > #blue + #green
constraint (sum (i in 0..tam-1 where (torre[i] = Red)) (1)) 
            >
           (sum (i in 0..tam-1) (bool2int((torre[i] = Blue) \/ (torre[i] = Green))));
   
solve satisfy;
                
output [ "\(torre[i]) "
         | i in 0..tam-1
];

%====================================================================
%output  [if torre[i] == 1 then "azul " else
%             (if torre[i] == 2 then "rojo " else "verde " endif)
%         endif | i in 0..tam-1 ];