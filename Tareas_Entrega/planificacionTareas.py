#!/usr/bin/python3

import sys

T = int(input())
D = int(input())
Lim = int(input())
dur1 = input().split()
dur = []
for i in range(T):
    dur.append(int(dur1[i]))

dep = []
for j in range(T):
    dep1 = input().split()
    dep2 = []
    for k in range(T):
        dep2.append(int(dep1[k]))
    dep.append(dep2)


def tarea (i):
    return "tarea_"+str(i)

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

def addplus(a1,a2):
    return "(+ "+a1+" "+a2+" )"

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

################################
# generamos un fichero smtlib2
################################

print("(set-option :produce-models true)")
print(setlogic("QF_LIA"))

#declaración de variables de la solución
for i in range(T):
    print(intvar(tarea(i)))
# fin declaración

#constraint forall (i in 0..T) (1 <= tarea_i);
#constraint forall (i in 0..T) (tarea_i <= Lim);
for i in range(T): # es equivalente a range(0,T)
    print(addassert(addle("1",tarea(i))))
    print(addassert(addle(tarea(i), str(Lim))))
#end constraint


#constraint assert (forall (i in 1..T) (duracion[i] <= D), "Alguna tarea se excede del maximo de duración");
for i in range(T): # es equivalente a range(0,tarea)
    print(addassert(addle(str(dur[i]) , str(D))))
#end constraint

#constraint forall(i in 1..T) ((asig[i] + duracion[i]) < Lim);
for i in range(T): # es equivalente a range(0,tarea)
    print(addassert(addlt(addplus(tarea(i), str(dur[i])) , str(Lim))))
#end constraint


#constraint forall(t in 1..T) ( forall(i in 1..T where dep[t, i] = 1)(asig[i]+duracion[i] <= asig[t]) );
for t in range(T):
    for i in range(T):
        if(dep[t][i] == 1):
            print(addassert(addle(addplus(tarea(i), str(dur[i])) , tarea(t))))
#fin constraint


checksat()

#getmodel()
for i in range(T):
    getvalue("("+tarea(i)+")")
exit(0)
