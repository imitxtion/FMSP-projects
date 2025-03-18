from z3 import *

################################################################################
# EXAMPLE 2

# Example program (annotated with pc values)
#
# initial constraints: x > 0 /\ y > 0 
#
# 1. z = y (0.);
# 2. WHILE 0 < x DO
# 4.   z = z + 1 (3.);
# 5.   x = x - 1
#    END

# Let's create the rules that represent the program
# and show examples of the rules that do not appear in it

# We declare predicates as (z3) functions to bool

# Predicates not in the programs
S_ = Function('S_', [IntSort(), IntSort(), IntSort(), BoolSort()])
E_ = Function('E_', [IntSort(), IntSort(), IntSort(), BoolSort()])
S_1 = Function('S_1', [IntSort(), IntSort(), IntSort(), BoolSort()])
E_1 = Function('E_1', [IntSort(), IntSort(), IntSort(), BoolSort()])
S_2 = Function('S_2', [IntSort(), IntSort(), IntSort(), BoolSort()])
E_2 = Function('E_2', [IntSort(), IntSort(), IntSort(), BoolSort()])

# Predicates describing the program
S0 = Function('S0', [IntSort(), IntSort(), IntSort(), BoolSort()])
E0 = Function('E0', [IntSort(), IntSort(), IntSort(), BoolSort()])
S1 = Function('S1', [IntSort(), IntSort(), IntSort(), BoolSort()])
E1 = Function('E1', [IntSort(), IntSort(), IntSort(), BoolSort()])
S2 = Function('S2', [IntSort(), IntSort(), IntSort(), BoolSort()])
E2 = Function('E2', [IntSort(), IntSort(), IntSort(), BoolSort()])
S3 = Function('S3', [IntSort(), IntSort(), IntSort(), BoolSort()])
S3 = Function('S3', [IntSort(), IntSort(), IntSort(), BoolSort()])
E3 = Function('E3', [IntSort(), IntSort(), IntSort(), BoolSort()])
S4 = Function('S4', [IntSort(), IntSort(), IntSort(), BoolSort()])
E4 = Function('E4', [IntSort(), IntSort(), IntSort(), BoolSort()])
S5 = Function('S5', [IntSort(), IntSort(), IntSort(), BoolSort()])
E5 = Function('E5', [IntSort(), IntSort(), IntSort(), BoolSort()])

# Let's declare some Int variables
x = Int('x')
y = Int('y')
z = Int('z')
x1 = Int('x1')
z1 = Int('z1')

# Empty Command Rule (not in the program so we use S_ and E_)
e = ForAll([x,y,z], Implies( S_(x,y,z), E_(x,y,z) ))

# Assignment (We have three assignments respectively at 1, 4, 5)
a1 = ForAll([x,y,z,z1], Implies( And( S1(x,y,z), z1 == y ), E1(x,y,z1) ))
a4 = ForAll([x,y,z,z1], Implies( And( S4(x,y,z), z1 == z + 1 ), E4(x,y,z1) ))
a5 = ForAll([x,y,z,x1], Implies( And( S5(x,y,z), x1 == x - 1 ), E5(x1,y,z) ))

# Composition (We have two compositions, at 0 and 3)
c0 = [ ForAll([x,y,z], Implies( S0(x,y,z), S1(x,y,z) )),
       ForAll([x,y,z], Implies( E1(x,y,z), S2(x,y,z) )),
       ForAll([x,y,z], Implies( E2(x,y,z), E0(x,y,z) )) ]
c3 = [ ForAll([x,y,z], Implies( S3(x,y,z), S4(x,y,z) )),
       ForAll([x,y,z], Implies( E4(x,y,z), S5(x,y,z) )),
       ForAll([x,y,z], Implies( E5(x,y,z), E3(x,y,z) )) ]

# IF (not in the program so we use S_ and E_)
EXPR = 1  # placeholder
i = [ ForAll([x,y,z], Implies( And( S_(x,y,z), EXPR != 0), S_1(x,y,z) )),
      ForAll([x,y,z], Implies( E_1(x,y,z), E_(x,y,z) )),
      ForAll([x,y,z], Implies( And( S_(x,y,z), EXPR == 0), S_2(x,y,z) )),
      ForAll([x,y,z], Implies( E_2(x,y,z), E_(x,y,z) )) ]

# While (In the program at 2)
w2 = [ ForAll([x,y,z], Implies( And( S2(x,y,z), 0 < x), S3(x,y,z) )),
       ForAll([x,y,z], Implies( E3(x,y,z), S2(x,y,z) )),
       ForAll([x,y,z], Implies( And( S2(x,y,z), Not(0 < x)), E2(x,y,z) )) ]

# We state that S0 is reachable if the initial conditions are true
initial = ForAll([x,y,z], Implies( And(x > 0, y > 0), S0(x,y,z) ))

# We query by adding an additional rule that is False when our property is false at the end of state E0.
# If x is not 0 at E0, our query would be False and the conjunction of all horn clauses and the query would be False (i.e., unsat).
# If x is always 0 at the end of the loop, the query would not be false, so the solver returns sat.
query = ForAll([x,y,z], Implies( And( E0(x,y,z), Not(x == 0) ), False ))

# We call the HORN clause solver of z3 by creating a specialized solver object
s = SolverFor('HORN')

# We then add all rules we previously defined (except those that do not appear in the program)
for rule in [c0,a1,w2,c3,a4,a5,initial,query]:
    s.add(rule)

# We check for satisfiability with the check() method:
# - a result of sat means that our set of rules is satisfiable, i.e., we could not derive False.
#   This means that our query (E0(x,y,z) /\ Not(x == 0)) is valid
# - a result of unsat means that we could derive False, so our query is not valid and a counterexample (x is 0) exists
print(s.check())
print(s.model())
