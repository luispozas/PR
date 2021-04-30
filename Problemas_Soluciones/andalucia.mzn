% Colouring Andalucia using nc colours
int: nc = 3;

var 1..nc: hu;   var 1..nc: se;  var 1..nc: co;   var 1..nc: ja;
var 1..nc: ca;  var 1..nc: ma;   var 1..nc: gr;   var 1..nc: al;

constraint hu != se;
constraint hu != ca;
constraint se != ca;
constraint se != ma;
constraint se != co;
constraint ca != ma;
constraint ma != co;
constraint ma != gr;
constraint co != ja;
constraint co != gr;
constraint gr != ja;
constraint gr != al;
%constraint hu != 2;
%constraint hu != 3;
%constraint hu != 1;

output ["hu=\(hu)\t se=\(se)\t co=\(co)\n",
        "ja=\(ja)\t ca=\(ca)\t ma=\(ma)\n",
        "gr=", show(gr), "\t ", "al=", show(al),  "\n"];
