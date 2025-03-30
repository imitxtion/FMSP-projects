from z3 import *

# Predicate declarations
# We only keep the predicates that appear in the program.
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

# Step 2: Introduce the Init predicate (for initial x and y)
Init = Function('Init', [IntSort(), IntSort(), BoolSort()])

# Declare some integer variables for use in rules
x   = Int('x')
y   = Int('y')
z   = Int('z')
x1  = Int('x1')
z1  = Int('z1')

# Assignment rules
# Rule a1 corresponds to the assignment "z = y" (line 1)
a1 = ForAll([x, y, z, z1],
    Implies(And(S1(x, y, z), z1 == y), E1(x, y, z1))
)
# Rule a4 corresponds to "z = z + 1" (line 4 inside the loop)
a4 = ForAll([x, y, z, z1],
    Implies(And(S4(x, y, z), z1 == z + 1), E4(x, y, z1))
)
# Rule a5 corresponds to "x = x - 1" (line 5 inside the loop)
a5 = ForAll([x, y, z, x1],
    Implies(And(S5(x, y, z), x1 == x - 1), E5(x1, y, z))
)

# Composition rules (sequence of program fragments)
# These “chain” the transitions together.
c0 = [
    ForAll([x, y, z], Implies(S0(x, y, z), S1(x, y, z))),
    ForAll([x, y, z], Implies(E1(x, y, z), S2(x, y, z))),
    ForAll([x, y, z], Implies(E2(x, y, z), E0(x, y, z)))
]
c3 = [
    ForAll([x, y, z], Implies(S3(x, y, z), S4(x, y, z))),
    ForAll([x, y, z], Implies(E4(x, y, z), S5(x, y, z))),
    ForAll([x, y, z], Implies(E5(x, y, z), E3(x, y, z)))
]

# While loop rules (for the loop starting at state S2)
w2 = [
    ForAll([x, y, z],
        Implies(And(S2(x, y, z), 0 < x), S3(x, y, z))
    ),
    ForAll([x, y, z],
        Implies(E3(x, y, z), S2(x, y, z))
    ),
    ForAll([x, y, z],
        Implies(And(S2(x, y, z), Not(0 < x)), E2(x, y, z))
    )
]

# Step 3: Init rule
# For all x and y greater than 0, the predicate Init(x,y) holds.
init_rule = ForAll([x, y],
    Implies(And(x > 0, y > 0), Init(x, y))
)

# Step 4: Modified initial rule
# Instead of directly checking x>0 and y>0, we require that Init(x,y) holds.
# Moreover, we force the initial state to have z == y (reflecting "z = y").
initial = ForAll([x, y, z],
    Implies(And(Init(x, y), z == y), S0(x, y, z))
)

# Step 5: New query
# We want to check the following property:
# "Given that Init holds for some initial values x0 and y0 and that E0(x,y,z) holds,
# can it be that z is not equal to x0 + y0?"
# In a correct run of the program the final state should satisfy z = x0 + y0.
x0, y0 = Ints('x0 y0')
query = ForAll([x0, y0, x, y, z],
    Implies(And(Init(x0, y0), E0(x, y, z), Not(z == x0 + y0)), False)
)

# Build the solver and add all rules
s = SolverFor('HORN')
for rule in [ initial, a1, a4, a5,
              c0[0], c0[1], c0[2],
              c3[0], c3[1], c3[2],
              w2[0], w2[1], w2[2],
              init_rule, query]:
    s.add(rule)

# Run the solver to check the query
result = s.check()
print(result)
if result == sat:
    print(f'\nModel:\n{s.model()}')
