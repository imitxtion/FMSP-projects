from z3 import *

# the variable cypher contains a sequence of characters that were encrypted by xor-ing them with some single-byte key `k`
# you know that the original plain text only contains lower case ASCII characters, i.e. number between 96 and 123 (exclusive)
cypher = [53, 38, 49, 58, 45, 42, 32, 38, 58, 44, 54, 39, 38, 32, 49, 58, 51, 55, 38, 39, 55, 43, 38, 32, 58, 51, 43, 38, 49, 55, 38, 59, 55, 48, 54, 32, 32, 38, 48, 48, 37, 54, 47, 47, 58]

# This creates a Z3 solver object. The solver will be used to find a solution that satisfies the constraints we define.
s = Solver()

# to model the all byte-level operations, we use SMT's BitVector-Theory
# we add a variable `k` to model the key
# BitVectors can be of various (constant) sizes, to get a byte (i.e., 8 bits)
# we use `8` as the second argument of the BitVec constructor

k = BitVec('k', 8)

# we additionally create one byte `v0`...`v(n-1)` for all `n` characters in the cypher text
# This creates a list of bitvector variables vs. Each variable v represents a byte of the original plaintext message.
vs = [BitVec('v' + str(i), 8) for i in range(len(cypher))]

for (v,c) in zip(vs, cypher):
    # whatever the key might be, `c xor k` should equal `v` for every pair of cypher-text-byte `c` and plain-text-byte `v`
    # adds a restriction to the solver that the XOR of each ciphertext byte c and the key k must equal the corresponding plaintext byte v.
    s.add(c ^ k == v)

    # now you have to add similar restrictions on `v` that express, that it is a lower-case-ASCII-character
    # you can add restrictions using the normal symbols you know from python (`<`, `>`, etc.)
    s.add(v >= 97, v <= 122)
    
# in case the problem is underconstrained, z3 might find the wrong key on the first try
# you can exclude wrong keys explicitly
#s.add(k != ...)

# This instructs the solver to check if there is a solution that satisfies all the constraints. 
# It returns sat if a solution is found, and unsat if no solution exists.
print(s.check())
# If a solution is found, this line retrieves the model (the solution) from the solver. 
# The model contains the values of the variables that satisfy the constraints.
m = s.model()

print(f"key: {m[k]}") # retrieves the value of the key from the mode
msg = "".join([chr(m[v].as_long()) for v in vs]) # converts the plaintext byte values back into characters.
print(f"message: {msg}")

