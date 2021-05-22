#!/usr/bin/python3

import sys

meses = int(input())
veg = int(input())
anv = int(input())
aceites = veg + anv
precios = []
for i in range(meses):
    vals = input().split()
    precios_aux = []
    for p in vals:
        precios_aux.append(int(p))
    precios.append(precios_aux)

VALOR = int(input())

MAXV = int(input())
MAXN = int(input())

MCAP = int(input())

CA = int(input())

minD = int(input())
maxD = int(input())

durezas = []
durezas_aux = input().split()
for i in range(len(durezas_aux)):
    durezas.append(float(durezas_aux[i]))

inicio = []
inicio_aux = input().split()
for i in range(len(inicio_aux)):
    inicio.append(int(inicio_aux[i]))

MinB = int(input())

K = int(input())
T = int(input())


# Parte de funciones smt
def compra(i, j):
    return "compra_"+str(i)+"_"+str(j)

def refina(i, j):
    return "refina_"+str(i)+"_"+str(j)

def almacen(i, j):
    return "almacen"+str(i)+"_"+str(j)

def setlogic(l):
    return "(set-logic "+ l +")"

def intvar(v):
    return "(declare-fun "+v+" () Int)"

def bool2int(b):
    return "(ite "+b+" 1 0 )"

def addand(a1,a2):
    return "(and "+a1+" "+a2+" )"
def addor(a1,a2):
    return "(or "+a1+" "+a2+" )"
def addnot(a):
    return "(not "+a+" )"

def addexists(a):
    if len(a) == 0:
        return "false"
    elif len(a) == 1:
        return a[0]
    else :
        x = a.pop()
        return "(or " + x + " " + addexists(a) + " )" 

def addeq(a1,a2):
    return "(= "+a1+" "+a2+" )" 
def addle(a1,a2):
    return "(<= "+a1+" "+a2+" )" 
def addge(a1,a2):
    return "(>= "+a1+" "+a2+" )" 
def addlt(a1,a2):
    return "(< "+a1+" "+a2+" )"
def addgt(a1,a2):
    return "(> "+a1+" "+a2+" )" 

def addminus(a1, a2):
    return "(- "+a1+" "+a2+" )"

def addplus(a1,a2):
    return "(+ "+a1+" "+a2+" )"

def addmul(a1, a2):
    return "(* "+a1+" "+a2+" )"

def addassert(a):
    return "(assert "+a+" )"

def addsum(a):
    if len(a) == 0:
        return "0"
    elif len(a) == 1:
        return a[0]
    else :
        x = a.pop()
        return "(+ " + x + " " + addsum(a) + " )" 

def checksat():
    print("(check-sat)")
def getmodel():
    print("(get-model)")
def getvalue(l):
    print("(get-value " + l + " )")
def maximize(w):
    print("(maximize " + w + " )")
def minimize(w):
    print("(minimize " + w + " )")

################################
# generamos un fichero smtlib2
################################

print("(set-option :produce-models true)")
#print(setlogic("QF_LIA"))

#Declaración de variables de la solucion
for i in range(meses):
    for j in range(aceites):
        print(intvar(compra(i, j)))
        print(intvar(almacen(i, j)))
        print(intvar(refina(i, j)))
# fin declaración

# Limites de la solucion
for i in range(meses):
    for j in range(aceites):
        print(addassert(addle(str(0), (compra(i, j)))))
        print(addassert(addge(str(MCAP), (compra(i, j)))))
        print(addassert(addle(str(0), (almacen(i, j)))))
        print(addassert(addge(str(MCAP), (almacen(i, j)))))
        print(addassert(addle(str(0), (refina(i, j)))))
        print(addassert(addge(str(MCAP), (refina(i, j)))))

#constraint forall(i in 1..meses) (sum(j in 1..veg) (refina[i,j]) <= MAXV);
for i in range(meses):
    suma = []
    for j in range(veg):
        suma.append(refina(i, j))
    print(addassert(addle(addsum(suma), str(MAXV))))

#constraint forall(i in 1..meses) (sum(j in veg+1..aceites) (refina[i,j]) <= MAXN);
for i in range(meses):
    suma = []
    for j in range(veg, aceites):
        suma.append(refina(i, j))
    print(addassert(addle(addsum(suma), str(MAXN))))

#constraint forall(i in 1..meses, j in 1..aceites) (refina[i,j] <= almacen[i,j] /\ almacen[i, j] <= MCAP);
for i in range(meses):
    for j in range(aceites):
        print (addassert(addand(addle(refina(i, j), almacen(i, j)), addle(almacen(i, j), str(MCAP)))))

#constraint forall(j in 1..aceites)(almacen[1,j] =  compra[1,j] + inicio[j] - refina[1,j]);
for j in range(aceites):
    print(addassert(addeq(almacen(1, j), addplus(compra(1, j), addminus(str(inicio[j]), refina(1, j))) )))

#constraint forall(i in 2..meses, j in 1..aceites)(almacen[i,j] = compra[i,j] + almacen[i-1,j] - refina[i,j]);
for i in range(1, meses):
    for j in range(aceites):
        print(addassert(addeq(almacen(i, j), addplus(compra(i, j), addminus(almacen(i-1, j), refina(1, j))) )))

#constraint forall(i in 1..aceites)(inicio[i] = almacen[meses,i]);
for j in range(aceites):
    print(addassert(addeq(str(inicio[j]), almacen(meses-1, j))))

# --------------------------------------------------------------------------------
#   El siguiente constraint:
#       'constraint forall(i in 1..meses) 
#               (comprobarDureza(sum(j in 1..aceites)(refina[i,j]*durezas[j]), 
#                                sum(j in 1..aceites)(refina[i,j])));' 
#   lo divido en dos mas simples de traducir a SMT2 que son los siguientes...
# --------------------------------------------------------------------------------

#constraint forall(i in 1..meses) (sum(j in 1..aceites)(refina[i,j]*durezas[j]) >= MinD*sum(j in 1..aceites)(refina[i,j]));
#constraint forall(i in 1..meses) (sum(j in 1..aceites)(refina[i,j]*durezas[j]) <= MaxD*sum(j in 1..aceites)(refina[i,j]));
for i in range(meses):
    sumaMinD = []
    sumaMaxD = []
    for j in range(aceites):
        sumaMinD.append(addmul(refina(i, j), str(durezas[j])))
        sumaMaxD.append(refina(i, j))
    print(addassert(addge(addsum(sumaMinD), addmul(str(minD), addsum(sumaMaxD)))))
    print(addassert(addle(addsum(sumaMinD), addmul(str(maxD), addsum(sumaMaxD)))))


# --------------------------------------------------------------------------------
#   El siguiente constraint:
#       'constraint (calcularBeneficio() - calcularGastos()) >= MinB;'
#   lo tranformo a los siguientes:
# --------------------------------------------------------------------------------

#constraint (sum(i in 1..meses, j in 1..aceites)(refina[i,j]*VALOR)) - 
#           (sum(i in 1..meses, j in 1..aceites)(almacen[i,j]*CA + compra[i,j]*precios[i,j])) 
#           >= MinB;
for i in range(meses):
    sumaB = []
    sumaC = []
    for j in range(aceites):
        sumaB.append(addmul(refina(i, j), str(VALOR)))
        sumaC.append(addplus(addmul(almacen(i, j), str(CA)), addmul(compra(i, j), str(precios[i][j]))))
    print(addassert(addge(addminus(addsum(sumaB), addsum(sumaC)), str(MinB))))


checksat()

#getmodel()
for i in range(meses):
    
    for j in range(aceites):
        getvalue("("+compra(i, j)+")")
        getvalue("("+refina(i, j)+")")
        getvalue("("+almacen(i, j)+")")
exit(0)