from z3 import *

# Declarations
ll = Solver()
F = DeclareSort('F')
entails = Function('entails', F, F, BoolSort())
par = Function('par', F, F, F)
tensor = Function('tensor', F, F, F)
lpop = Function('lollipop', F, F, F)
oplus = Function("oplus", F, F, F)
amp = Function("with", F, F, F)
dual = Function('dual', F, F)
em = Function("em", F, F)
x, y, z, w, I, Top= Consts('x y z w I Top', F)

# Given rules
ll.add(ForAll([x], entails(x, x)))  # rule (i)
ll.add(ForAll([x, y, z], Implies(And(entails(x, y), entails(y, z)), entails(x, z))))  # rule (o)
ll.add(ForAll([w, x, y, z], Implies(And(entails(w, x), entails(y, z)), entails(tensor(w, y), tensor(x, z)))))  # rule (tensor)
ll.add(ForAll([w, x, y, z], entails(w, tensor(tensor(x, y), z)) == entails(w, tensor(x, tensor(y, z)))))  # rule (a)
ll.add(ForAll([x, y], entails(x, tensor(I, y)) == entails(x, y)))  # rule (l)
ll.add(ForAll([x, y], entails(x, tensor(y, I)) == entails(x, y)))  # rule (r)
ll.add(ForAll([w, x, y], entails(w, tensor(x, y)) == entails(w, tensor(y, x))))  # rule (b)
ll.add(ForAll([x, y, z], entails(tensor(x, y), z) == entails(y, lpop(x, z))))  # rule (c)

# Derived rules (commented out)
# ll.add(Not(ForAll([x, y], entails(tensor(x, lpop(x, y)), y))))  # rule (ev)
# ll.add(Not(ForAll([x, y, z], entails(tensor(lpop(x, y), lpop(y, z)), lpop(x, z)))))  # internal composition rule

# Given rules for dual and par
ll.add(ForAll([x], dual(x) == lpop(x, I)))  # dual
ll.add(ForAll([x, y], par(x, y) == lpop(dual(x), y)))  # par

# Proving properties of dual and par (commented out examples)
# ll.add(Not(ForAll([x], entails(x, dual(dual(x))))))  # x |- x dual dual
# ll.add(Not(ForAll([x, y], entails(par(dual(x), y), lpop(x, y)))))  # X dual par Y |- X -o Y
# ll.add(Not(ForAll([x, y], entails(par(x, y), dual(tensor(dual(x), dual(y)))))))  # x par y |- -( - x tensor - y)
# ll.add(Not(entails(dual(I), I)))
# ll.add(Not(entails(I, dual(I))))
# ll.add(Not(ForAll([x], entails(x, par(x, I)))))

#oplus R
ll.add(ForAll([x, y, z], Implies(entails(x, y), entails(x, oplus(y,z)))))
ll.add(ForAll([x, y, z], Implies(entails(x, z), entails(x, oplus(y,z)))))

#oplus L
ll.add(ForAll([x, y, z], Implies(And(entails(x, y), entails(z,y)), entails(oplus(x,z), y))))

#amp L
ll.add(ForAll([x, y, z], Implies(entails(x, y), entails(amp(x,z), y))))
ll.add(ForAll([x, y, z], Implies(entails(z, y), entails(amp(x,z), y))))

#amp R
ll.add(ForAll([x, y, z], Implies(And(entails(x, y), entails(x,z)), entails(x, oplus(y,z)))))

#Top
ll.add(ForAll([x], entails(x, Top)))


# Verification
print(ll.check())
if ll.check() == sat:
    print(ll.model())

ll.add(Not(ForAll([x], entails(I, lpop(x,x)))))
print(ll.check())
