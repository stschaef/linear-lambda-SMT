from z3 import *

set_option(proof=True)

x = Int('x')
y = Int('y')

s = Solver()
s.add(x > y)
s.add(x < y)

if s.check() == unsat:
    print("Proof:")
    print(s.proof())
else:
    print("The formula is satisfiable.")