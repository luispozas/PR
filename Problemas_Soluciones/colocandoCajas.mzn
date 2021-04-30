par int: X;
par int: Y;

par int: N;
array[1..N, 1..2] of int: dims; 


array[1..N] of var 0..(X-1): asigX;
array[1..N] of var 0..(Y-1): asigY;

constraint assert( sum (i in 1..N) (dims[i,1]*dims[i,2]) = X*Y, "No se puede cubrir toda la superficie");

constraint forall(i in 1..N) (dims[i, 1] + asigX[i] <= X);
constraint forall(i in 1..N) (dims[i, 2] + asigY[i] <= Y);

% No hay piezas situadas en la misma posicion
constraint forall(i in 1..N, j in 1..N where i != j) (not (asigX[i] = asigX[j] /\ asigY[i] = asigY[j]));
                     
                                                                                       

%No hay solapamiento entre cajas
constraint forall (c1, c2 in 1..N where asigX[c1] < asigX[c2]) (asigX[c1]+(dims[c1,1]-1) < asigX[c2] /\ 
                                                                asigY[c1]+(dims[c1,2]-1) > asigY[c2]    );


solve satisfy;

output [ "\(asigX[i]) \(asigY[i])\n" | i in 1..N ];
