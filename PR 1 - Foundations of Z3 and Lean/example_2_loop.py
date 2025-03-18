from z3 import *

z3.set_param(proof=True)

################################################################################
# EXAMPLE 2

# Example program (annotated with pc values)
#
# initial values: x0, y0
# initial constraints: x0 > 0 /\ y0 > 0 /\ x = x0 /\ y = y0
#
# 1. z = y (0.);
# 2. WHILE 0 < x DO
# 4.   z = z + 1 (3.);
# 5.   x = x - 1
#    END

# Let's create the rules that represent the program

# Predicates describing the program 
# (now we need 5 parameters to also keep around the initial values)
S0 = Function('S0', [IntSort(), IntSort(), IntSort(), IntSort(), IntSort(), BoolSort()])
E0 = Function('E0', [IntSort(), IntSort(), IntSort(), IntSort(), IntSort(), BoolSort()])
S1 = Function('S1', [IntSort(), IntSort(), IntSort(), IntSort(), IntSort(), BoolSort()])
E1 = Function('E1', [IntSort(), IntSort(), IntSort(), IntSort(), IntSort(), BoolSort()])
S2 = Function('S2', [IntSort(), IntSort(), IntSort(), IntSort(), IntSort(), BoolSort()])
E2 = Function('E2', [IntSort(), IntSort(), IntSort(), IntSort(), IntSort(), BoolSort()])
S3 = Function('S3', [IntSort(), IntSort(), IntSort(), IntSort(), IntSort(), BoolSort()])
S3 = Function('S3', [IntSort(), IntSort(), IntSort(), IntSort(), IntSort(), BoolSort()])
E3 = Function('E3', [IntSort(), IntSort(), IntSort(), IntSort(), IntSort(), BoolSort()])
S4 = Function('S4', [IntSort(), IntSort(), IntSort(), IntSort(), IntSort(), BoolSort()])
E4 = Function('E4', [IntSort(), IntSort(), IntSort(), IntSort(), IntSort(), BoolSort()])
S5 = Function('S5', [IntSort(), IntSort(), IntSort(), IntSort(), IntSort(), BoolSort()])
E5 = Function('E5', [IntSort(), IntSort(), IntSort(), IntSort(), IntSort(), BoolSort()])

# Let's declare some Int variables
x0 = Int('x0')
y0 = Int('y0')
x = Int('x')
y = Int('y')
z = Int('z')
x1 = Int('x1')
z1 = Int('z1')

# Assignment (We have three assignments respectively at 1, 4, 5)
a1 = ForAll([x0,y0,x,y,z,z1], Implies( And( S1(x0,y0,x,y,z), z1 == y ),     E1(x0,y0,x,y,z1) ))
a4 = ForAll([x0,y0,x,y,z,z1], Implies( And( S4(x0,y0,x,y,z), z1 == z + 1 ), E4(x0,y0,x,y,z1) ))
a5 = ForAll([x0,y0,x,y,z,x1], Implies( And( S5(x0,y0,x,y,z), x1 == x - 1 ), E5(x0,y0,x1,y,z) ))

# Composition (We have two compositions, at 0 and 3)
c0 = [ ForAll([x0,y0,x,y,z], Implies( S0(x0,y0,x,y,z), S1(x0,y0,x,y,z) )),
       ForAll([x0,y0,x,y,z], Implies( E1(x0,y0,x,y,z), S2(x0,y0,x,y,z) )),
       ForAll([x0,y0,x,y,z], Implies( E2(x0,y0,x,y,z), E0(x0,y0,x,y,z) )) ]
c3 = [ ForAll([x0,y0,x,y,z], Implies( S3(x0,y0,x,y,z), S4(x0,y0,x,y,z) )),
       ForAll([x0,y0,x,y,z], Implies( E4(x0,y0,x,y,z), S5(x0,y0,x,y,z) )),
       ForAll([x0,y0,x,y,z], Implies( E5(x0,y0,x,y,z), E3(x0,y0,x,y,z) )) ]

# While (In the program at 2)
w2 = [ ForAll([x0,y0,x,y,z], Implies( And( S2(x0,y0,x,y,z), 0 < x), S3(x0,y0,x,y,z) )),
       ForAll([x0,y0,x,y,z], Implies( E3(x0,y0,x,y,z), S2(x0,y0,x,y,z) )),
       ForAll([x0,y0,x,y,z], Implies( And( S2(x0,y0,x,y,z), Not(0 < x)), E2(x0,y0,x,y,z) )) ]


initial = ForAll([x0,y0,x,y,z], Implies( And(x0 > 0, y0 > 0, x == x0, y == y0), S0(x0,y0,x,y,z) ))
query = ForAll([x0,y0,x,y,z], Implies( And( E0(x0,y0,x,y,z), Not(z == x0+y0) ), False ))


s = SolverFor('HORN')

for rule in [c0,a1,w2,c3,a4,a5,initial,query]:
    s.add(rule)

print(s.check())
