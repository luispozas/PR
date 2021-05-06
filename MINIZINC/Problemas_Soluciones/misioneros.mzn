% LUIS POZAS PALOMO
int: N = 11;

array [1..N] of var 0..2: movC;
array [1..N] of var 0..2: movM;
array [1..N+1] of var 0..3: CA;
array [1..N+1] of var 0..3: MA;
array [1..N+1] of var 0..3: CB;
array [1..N+1] of var 0..3: MB;

constraint CA[1] = 3 /\ MA[1] = 3;

constraint CB[N+1] = 3 /\ MB[N+1] = 3;

constraint forall(i in 1..N+1)(if(MA[i] > 0 /\ MB[i] > 0) then (CA[i] <= MA[i] /\ CB[i] <= MB[i]) endif);

constraint forall(i in 1..N+1)(
               (CA[i] + CB[i]) = 3 /\ 
               (MA[i] + MB[i]) = 3);

constraint forall(i in 1..N)(
               (movC[i] + movM[i]) <= 2 /\ 
               (movC[i] + movM[i]) >= 1);

constraint forall(i in 1..N where (i mod 2) = 1)(CB[i+1] = (CB[i] + movC[i]) /\
                                                 MB[i+1] = (MB[i] + movM[i])    );

constraint forall(i in 1..N where (i mod 2) = 0)(CA[i+1] = (CA[i] + movC[i]) /\ 
                                                 MA[i+1] = (MA[i] + movM[i])    );

solve satisfy;
