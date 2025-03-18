from z3 import *

################################################################################
# EXAMPLE 2 - Modified with Init predicate approach

# Example program (annotated with pc values)
#
# initial constraints: x > 0 /\ y > 0 
#
# 1. z = y (0.);
# 2. WHILE 0 < x DO
# 4.   z = z + 1 (3.);
# 5.   x = x - 1
#    END

# We declare predicates as (z3) functions to bool
# Predicates describing the program
S0 = Function('S0', [IntSort(), IntSort(), IntSort(), BoolSort()])
E0 = Function('E0', [IntSort(), IntSort(), IntSort(), BoolSort()])
S1 = Function('S1', [IntSort(), IntSort(), IntSort(), BoolSort()])
E1 = Function('E1', [IntSort(), IntSort(), IntSort(), BoolSort()])
S2 = Function('S2', [IntSort(), IntSort(), IntSort(), BoolSort()])
E2 = Function('E2', [IntSort(), IntSort(), IntSort(), BoolSort()])
S3 = Function('S3', [IntSort(), IntSort(), IntSort(), BoolSort()])
E3 = Function('E3', [IntSort(), IntSort(), IntSort(), BoolSort()])
S4 = Function('S4', [IntSort(), IntSort(), IntSort(), BoolSort()])
E4 = Function('E4', [IntSort(), IntSort(), IntSort(), BoolSort()])
S5 = Function('S5', [IntSort(), IntSort(), IntSort(), BoolSort()])
E5 = Function('E5', [IntSort(), IntSort(), IntSort(), BoolSort()])

# New Init predicate to store initial values
Init = Function('Init', [IntSort(), IntSort(), BoolSort()])

# Let's declare some Int variables
x = Int('x')
y = Int('y')
z = Int('z')
x0 = Int('x0')  # Initial value of x
y0 = Int('y0')  # Initial value of y
x1 = Int('x1')
z1 = Int('z1')

# Rule for Init: Init(x,y) is true for all x and y greater than 0
init_rule = ForAll([x, y], Implies(And(x > 0, y > 0), Init(x, y)))

# Assignment (We have three assignments respectively at 1, 4, 5)
a1 = ForAll([x,y,z,z1], Implies(And(S1(x,y,z), z1 == y), E1(x,y,z1)))
a4 = ForAll([x,y,z,z1], Implies(And(S4(x,y,z), z1 == z + 1), E4(x,y,z1)))
a5 = ForAll([x,y,z,x1], Implies(And(S5(x,y,z), x1 == x - 1), E5(x1,y,z)))

# Composition (We have two compositions, at 0 and 3)
c0 = [ForAll([x,y,z], Implies(S0(x,y,z), S1(x,y,z))),
      ForAll([x,y,z], Implies(E1(x,y,z), S2(x,y,z))),
      ForAll([x,y,z], Implies(E2(x,y,z), E0(x,y,z)))]
c3 = [ForAll([x,y,z], Implies(S3(x,y,z), S4(x,y,z))),
      ForAll([x,y,z], Implies(E4(x,y,z), S5(x,y,z))),
      ForAll([x,y,z], Implies(E5(x,y,z), E3(x,y,z)))]

# While (In the program at 2)
w2 = [ForAll([x,y,z], Implies(And(S2(x,y,z), 0 < x), S3(x,y,z))),
      ForAll([x,y,z], Implies(E3(x,y,z), S2(x,y,z))),
      ForAll([x,y,z], Implies(And(S2(x,y,z), Not(0 < x)), E2(x,y,z)))]

# Modified initial rule: S0(x,y,z) is true for all x and y such that Init(x,y) holds
initial = ForAll([x, y, z], Implies(Init(x, y), S0(x, y, z)))

# New query: Given that Init is true for x0 and y0, and E0 is true for x, y, and z,
# can it be the case that z is not equal to x0+y0?
query = ForAll([x0, y0, x, y, z], Implies(And(Init(x0, y0), E0(x, y, z), Not(z == x0 + y0)), False))

# We call the HORN clause solver of z3 by creating a specialized solver object
s = SolverFor('HORN')

# We then add all rules we previously defined
for rule in [init_rule, c0, a1, w2, c3, a4, a5, initial, query]:
    s.add(rule)

print("Result:", s.check())
if s.check() == sat:
    print("Model:", s.model())
