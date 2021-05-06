% sudoku table 4x4
array[0..3,0..3] of var 1..4: sudoku;

% condition on rows
constraint forall (i in 0..3, j in 0..3, k in j+1..3) 
           (sudoku[i,j] != sudoku[i,k]);

% condition on columns
constraint forall (j in 0..3, i in 0..3, k in i+1..3) 
           (sudoku[i,j] != sudoku[k,j]);

%condition on squares
constraint forall (c1,c2 in {0,2}, i,i1 in {c1,c1+1}, j,j1 in {c2,c2+1}  where (i!=i1 \/ j!=j1))
	          (sudoku[i,j] != sudoku[i1,j1]);

%initial configuration
constraint sudoku[0,1] = 3;
constraint sudoku[0,2] = 4;
constraint sudoku[1,3] = 2;
constraint sudoku[2,0] = 1;
constraint sudoku[2,3] = 3;
constraint sudoku[3,1] = 2;
constraint sudoku[3,2] = 1;

% Solve 
solve satisfy;

output [ "\(sudoku[i,j])" ++ 
         if j == 3 then "\n" else " " endif |
         i in 0..3, j in 0..3
];
