## Importing the z3 module
from z3 import *

## Declarations
ll = Solver()
F = DeclareSort("F")
entails = Function("entails", F, F, BoolSort())
tensor = Function("tensor", F, F, F)
lpop = Function("lollipop", F, F, F)
par = Function("par", F, F, F)  # For the ⅋ connective
comma = Function('comma', F, F, F)


# Variables
x, y, z = Consts('x y z', F)
delta = Const('delta', F)
gamma = Const('gamma', F)
delta1, delta2 = Consts('delta1 delta2', F)
gamma1, gamma2 = Consts('gamma1 gamma2', F)
B1, B2 = Consts('B1 B2', F)
x, y, z, Gamma, Gamma1, Gamma2, Delta, Delta1, Delta2, B, B1, B2, zero, Top = Consts(
    "x y z Gamma Gamma1 Gamma2 Delta Delta1 Delta2 B B1 B2 zero Top", F
)

# Constants
one = Const('1', F)
bot = Const('⊥', F)
empty = Const('empty', F)

## Identity Rules
ll.add(ForAll([x], entails(x, x)))  # (i)
ll.add(
    ForAll(
        [x, y, z], entails(tensor(x, y), z) == entails(y, lpop(x, z))
    )
)  # (c)

## Multiplicative Rules

# Rule 1 (1L)
ll.add(ForAll([delta, gamma], Implies(entails(delta, gamma), entails(comma(delta, one), gamma))))

# Rule 2 (1R)
ll.add(entails(empty, one))

# Rule 3 (⊥L)
ll.add(entails(bot, empty))

# Rule 4 (⊥R)
ll.add(ForAll([delta, gamma], Implies(entails(delta, gamma), entails(delta, comma(bot, gamma)))))

# Rule 5 (⊗L)
ll.add(ForAll([delta, gamma, B1, B2],
              Implies(entails(comma(comma(delta, B1), B2), gamma),
                      entails(comma(delta, tensor(B1, B2)), gamma))))

# Rule 6 (⊗R)
ll.add(ForAll([delta1, delta2, gamma1, gamma2, B1, B2],
              Implies(And(entails(delta1, comma(B1, gamma1)), entails(delta2, comma(B2, gamma2))),
                      entails(comma(delta1, delta2), comma(tensor(B1, B2), comma(gamma1, gamma2))))))

# Rule 7 (⅋L)
ll.add(ForAll([delta1, delta2, gamma1, gamma2, B1, B2],
              Implies(And(entails(comma(delta1, B1), gamma1), entails(comma(delta2, B2), gamma2)),
                      entails(comma(comma(delta1, delta2), par(B1, B2)), comma(gamma1, gamma2)))))

# Rule 8 (⅋R)
ll.add(ForAll([delta, gamma, B1, B2],
              Implies(entails(delta, comma(B1, comma(B2, gamma))),
                      entails(delta, comma(par(B1, B2), gamma)))))

### Additive Rules ###
oplus = Function("oplus", F, F, F)
amp = Function("with", F, F, F)

# 0L
ll.add(ForAll([Delta, Gamma], entails(comma(Delta, zero), Gamma)))

# TR
ll.add(ForAll([Delta, Gamma], entails(Delta, comma(Top, Gamma))))

# &L(i = 1,2)
ll.add(
    ForAll(
        [Delta, B1, B2, Gamma],
        Implies(
            entails(comma(Delta, B2), Gamma),
            entails(comma(Delta, amp(B1, B2)), Gamma),
        ),
    )
)

ll.add(
    ForAll(
        [Delta, B1, B2, Gamma],
        Implies(
            entails(comma(Delta, B1), Gamma),
            entails(comma(Delta, amp(B1, B2)), Gamma),
        ),
    )
)

# &R
ll.add(
    ForAll(
        [Delta, B1, B2, Gamma],
        Implies(
            And(
                entails(Delta, comma(B1, Gamma)),
                entails(Delta, comma(B2, Gamma)),
            ),
            entails(Delta, comma(amp(B1, B2), Gamma)),
        ),
    )
)

# (+)L
ll.add(
    ForAll(
        [Delta, B1, B2, Gamma],
        Implies(
            And(
                entails(comma(Delta, B1), Gamma),
                entails(comma(Delta, B2), Gamma),
            ),
            entails(comma(Delta, oplus(B1, B2)), Gamma),
        ),
    )
)

# (+)R(i = 1,2)
ll.add(
    ForAll(
        [Delta, B1, B2, Gamma],
        Implies(
            entails(Delta, comma(B2, Gamma)),
            entails(Delta, comma(oplus(B1, B2), Gamma)),
        ),
    )
)

ll.add(
    ForAll(
        [Delta, B1, B2, Gamma],
        Implies(
            entails(Delta, comma(B1, Gamma)),
            entails(Delta, comma(oplus(B1, B2), Gamma)),
        ),
    )
)

### Exponential Rules ###
em = Function("em", F, F)
qm = Function("qm", F, F)

# !W
ll.add(
    ForAll(
        [Delta, Gamma, B],
        Implies(
            entails(Delta, Gamma),
            entails(comma(Delta, em(B)), Gamma),
        ),
    )
)

# !C
ll.add(
    ForAll(
        [Delta, Gamma, B],
        Implies(
            entails(comma(Delta, comma(em(B), em(B))), Gamma),
            entails(comma(Delta, em(B)), Gamma),
        ),
    )
)

# !D
ll.add(
    ForAll(
        [Delta, Gamma, B],
        Implies(
            entails(comma(Delta, B), Gamma),
            entails(comma(Delta, em(B)), Gamma),
        ),
    )
)

# !R
ll.add(
    ForAll(
        [Delta, Gamma, B],
        Implies(
            entails(em(Delta), comma(B, qm(Gamma))),
            entails(em(Delta), comma(em(B), qm(Gamma))),
        ),
    )
)

# ?W
ll.add(
    ForAll(
        [Delta, Gamma, B],
        Implies(
            entails(Delta, Gamma),
            entails(Delta, comma(qm(B), Gamma)),
        ),
    )
)

# ?C
ll.add(
    ForAll(
        [Delta, Gamma, B],
        Implies(
            entails(Delta, comma(comma(qm(B), qm(B)), Gamma)),
            entails(Delta, comma(qm(B), Gamma)),
        ),
    )
)

# ?D
ll.add(
    ForAll(
        [Delta, Gamma, B],
        Implies(
            entails(Delta, comma(B, Gamma)),
            entails(Delta, comma(qm(B), Gamma)),
        ),
    )
)

# ?L
ll.add(
    ForAll(
        [Delta, Gamma, B],
        Implies(
            entails(comma(em(Delta), B), qm(Gamma)),
            entails(comma(em(Delta), qm(B)), qm(Gamma)),
        ),
    )
)


print(ll.check())

# test_solver = Solver()

# test_solver.add(ll.assertions())

# test_solver.add(Implies(entails(lpop(x,x), gamma), entails(lpop(x,x), comma(bot, gamma))))

# print(test_solver.check())
