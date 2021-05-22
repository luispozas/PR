# LUIS POZAS PALOMO - PR - PRUEBA 20 MAYO
# -----------------------------------------------------
# Para ejecutar el código podéis hacer lo siguiente:
# python3 escuchandoMusica.py < input1.txt > escuchandoMusica.smt2
# z3 escuchandoMusica.smt2
# -----------------------------------------------------

#!/usr/bin/python3

import sys

N = int(input())
t1 = int(input())
t2 = int(input())
min_sat = int(input())

dursat = []
for i in range(N):
    ds = input().split()
    dursat_aux = []
    dursat_aux.append(int(ds[0]))
    dursat_aux.append(int(ds[1]))
    dursat.append(dursat_aux)

# SOLUCION:
# =========
# 0 -> no reproduce
# 1 -> viaje de ida
# 2 -> viaje de vuelta

def cancion(i):
    return "cancion_"+str(i)


def setlogic(l):
    return "(set-logic " + l + ")"

def intvar(v):
    return "(declare-fun "+v+" () Int)"

def boolvar(v):
    return "(declare-fun "+v+" () Bool)"

def bool2int(b):
    return "(ite "+b+" 1 0 )"

def addimplies(a1, a2):
    return "(=> "+a1+" "+a2+" )"

def addand(a1, a2):
    return "(and "+a1+" "+a2+" )"

def addor(a1, a2):
    return "(or "+a1+" "+a2+" )"

def addnot(a):
    return "(not "+a+" )"

def addexists(a):
    if len(a) == 0:
        return "false"
    elif len(a) == 1:
        return a[0]
    else:
        x = a.pop()
        return "(or " + x + " " + addexists(a) + " )"

def addeq(a1, a2):
    return "(= "+a1+" "+a2+" )"

def adddistinct(a1, a2):
    return "(distinct "+a1+" "+a2+" )"

def addle(a1, a2):
    return "(<= "+a1+" "+a2+" )"

def addge(a1, a2):
    return "(>= "+a1+" "+a2+" )"

def addlt(a1, a2):
    return "(< "+a1+" "+a2+" )"

def addgt(a1, a2):
    return "(> "+a1+" "+a2+" )"

def addplus(a1, a2):
    return "(+ "+a1+" "+a2+" )"

def addminus(a1, a2):
    return "(- "+a1+" "+a2+" )"

def addmul(a1, a2):
    return "(* "+a1+" "+a2+" )"

def addassert(a):
    return "(assert "+a+" )"

def addassertsoft(a, w):
    return "(assert-soft "+a+" :weight " + w + " )"

def addsum(a):
    if len(a) == 0:
        return "0"
    elif len(a) == 1:
        return a[0]
    else:
        x = a.pop()
        return "(+ " + x + " " + addsum(a) + " )"

def maximize(w):
    print("(maximize " + w + " )")

def checksat():
    print("(check-sat)")

def getobjectives():
    print("(get-objectives)")

def getmodel():
    print("(get-model)")

def getvalue(l):
    print("(get-value ( " + l + " ) )")

################################
# generamos un fichero smtlib2
################################

print("(set-option :produce-models true)")
#print(setlogic("QF_LIA"))

#declaración de variables de la solución
for i in range(N):
    print(intvar(cancion(i)))
# fin declaración

#constraint forall (i in 0..N) (0 <= cancion_i);
#constraint forall (i in 0..N) (cancion_i <= 2);
for i in range(N): # es equivalente a range(0,N)
    print(addassert(addle("0",cancion(i))))
    print(addassert(addle(cancion(i), "2")))
#end constraint

# constraint (sum(i in 1..N where asig[i] = 1)(dur_sat[i, 1])) <= t1;
sumt1 = []
for i in range(N):
    sumt1.append(addmul( bool2int(addeq(cancion(i), "1")) , str(dursat[i][0]) ))

print(addassert(addle(addsum(sumt1), str(t1))))


# constraint (sum(i in 1..N where asig[i] = 2)(dur_sat[i, 1])) <= t2;
sumt2 = []
for i in range(N):
    sumt2.append(addmul( bool2int(addeq(cancion(i), "2")) , str(dursat[i][0]) ))

print(addassert(addle(addsum(sumt2), str(t2))))


# constraint min_sat <=  ((sum(i in 1..N where asig[i] = 1)(dur_sat[i, 2]))
#                         + 
#                        (sum(j in 1..N where asig[j] = 2)(dur_sat[j, 2])));

sum1 = []
for i in range(N):
    sum1.append(addmul( bool2int(addeq(cancion(i), "1")) , str(dursat[i][1]) ))
    sum1.append(addmul( bool2int(addeq(cancion(i), "2")) , str(dursat[i][1]) ))


print(addassert(addle(str(min_sat), addsum(sum1))))


checksat()

#getmodel()
for i in range(N):
    getvalue(cancion(i))


exit(0)
