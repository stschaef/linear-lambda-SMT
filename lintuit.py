## Importing the z3 module
from z3 import *

## Declarations
ll = Solver()
F = DeclareSort("F")

entails = Function("entails", F, F, BoolSort())
tensor = Function("tensor", F, F, F)
lpop = Function("lollipop", F, F, F)
oplus = Function("oplus", F, F, F)
amp = Function("with", F, F, F)
star = Function("*", F, F)

# Variables
x, y, z, w = Consts('x y z w', F)
delta = Const('delta', F)
gamma = Const('gamma', F)
delta1, delta2 = Consts('delta1 delta2', F)
gamma1, gamma2 = Consts('gamma1 gamma2', F)
B1, B2 = Consts('B1 B2', F)
x, y, z, Gamma, Gamma1, Gamma2, Delta, Delta1, Delta2, B, B1, B2, zero, Top, I = Consts(
    "x y z Gamma Gamma1 Gamma2 Delta Delta1 Delta2 B B1 B2 zero Top I", F
)

# Constants
one = Const('1', F)
bot = Const('⊥', F)
empty = Const('empty', F)

ll.add(ForAll([x], entails(one, star(x))))
ll.add(ForAll([x], entails(tensor(x, star(x)), star(x))))
ll.add(ForAll([x], entails(tensor(star(x), x), star(x))))
ll.add(ForAll([x, y],
    Implies(
        And(entails(one, y), entails(tensor(x, star(x)), y)),
        entails(star(x), y)
    )
))
ll.add(ForAll([x, y],
    Implies(
        And(entails(one, y), entails(tensor(star(x), x), y)),
        entails(star(x), y)
    )
))

ll.add(
    ForAll(
        [x,y,z],
        entails(
            tensor(x,tensor(y,z)),
            tensor(tensor(x,y), z)
        )
    )
)

ll.add(
    ForAll(
        [x,y,z],
        entails(
            tensor(tensor(x,y), z),
            tensor(x,tensor(y,z))
        )
    )
)

ll.add(
    ForAll(
        [x,y,z],
        entails(
            tensor(oplus(x,y), z),
            oplus(tensor(x, z),tensor(y,z))
        )
    )
)
ll.add(
    ForAll(
        [x,y,z],
        entails(
            oplus(tensor(x, z),tensor(y,z)),
            tensor(oplus(x,y), z),
        )
    )
)

ll.add(
    ForAll(
        [x,y,z],
        entails(
            tensor(x, oplus(y,z)),
            oplus(tensor(x, y),tensor(x,z))
        )
    )
)

ll.add(
    ForAll(
        [x,y,z],
        entails(
            oplus(tensor(x, y),tensor(x,z)),
            tensor(x, oplus(y,z)),
        )
    )
)


## Identity Rules
ll.add(ForAll([x], entails(x, x)))  # (i)

# transitivity
ll.add(ForAll([x,y,z],
    Implies(
        And(entails(x, y), entails(y,z)),
        entails(x, z)
    )))

# lollipop
ll.add(
    ForAll(
        [x, y, z], entails(tensor(x, y), z) == entails(y, lpop(x, z))
    )
)

ll.add(ForAll([x],
    entails(tensor(one, x), x)))
ll.add(ForAll([x],
    entails(tensor(x, one), x)))
ll.add(ForAll([x],
    entails(x, tensor(one, x))))
ll.add(ForAll([x],
    entails(x, tensor(x, one))))

# Rule 6 (⊗R)
ll.add(ForAll([delta1, delta2, B1, B2],
    Implies(And(entails(delta1, B1), entails(delta2, B2)),
                entails(tensor(delta1, delta2), tensor(B1, B2)))))

# Rule 8 (⅋R)
# ll.add(ForAll([delta, gamma, B1, B2],
#               Implies(entails(delta, comma(B1, comma(B2, gamma))),
#                       entails(delta, comma(par(B1, B2), gamma)))))

### Additive Rules ###

ll.add(ForAll([x],
    entails(oplus(zero, x), x)))
ll.add(ForAll([x],
    entails(oplus(x, zero), x)))
ll.add(ForAll([x],
    entails(x, oplus(zero, x))))
ll.add(ForAll([x],
    entails(x, oplus(x, zero))))

ll.add(ForAll([x],
    entails(amp(Top, x), x)))
ll.add(ForAll([x],
    entails(amp(x, Top), x)))
ll.add(ForAll([x],
    entails(x, amp(Top, x))))
ll.add(ForAll([x],
    entails(x, amp(x, Top))))

# 0L
ll.add(ForAll([x], entails(zero, x)))

# TR
ll.add(ForAll([x], entails(x, Top))) 

# &R
ll.add(
    ForAll(
        [Delta, B1, B2],
        Implies(
            And(
                entails(Delta, B1),
                entails(Delta, B2)),
            entails(Delta, amp(B1, B2))
        )
    )
)
ll.add(
    ForAll(
        [Delta, B1, B2],
        Implies(
            entails(Delta, amp(B1, B2)),
            entails(Delta, B1)
        )
    )
)
ll.add(
    ForAll(
        [Delta, B1, B2],
        Implies(
            entails(Delta, amp(B1, B2)),
            entails(Delta, B2)
        )
    )
)

# (+)R(i = 1,2)
ll.add(
    ForAll(
        [Delta, B1, B2],
        Implies(
            entails(Delta, B2),
            entails(Delta, oplus(B1, B2))
        )
    ),
)

ll.add(
    ForAll(
        [Delta, B1, B2],
        Implies(
            entails(Delta, B1),
            entails(Delta, oplus(B1, B2))
        )
    ),
)

ll.add(
    ForAll(
        [x,y,z,w],
        Implies(
            And(
                entails(w, oplus(x,y)),
                entails(x,z),
                entails(y,z)
            ),
            entails(w,z)
        )
    )
)

### Exponential Rules ###
# qm = Function("qm", F, F)

# ll.add(ForAll([x], entails(x, em(x))))
# ll.add(ForAll([x], entails(em(x), tensor(em(x), em(x)))))
# ll.add(ForAll([x], entails(tensor(em(x), em(x)), em(x))))

# !W
# ll.add(
#     ForAll(
#         [Delta, Gamma, B],
#         Implies(
#             entails(Delta, Gamma),
#             entails(comma(Delta, em(B)), Gamma),
#         ),
#     )
# )

# # !C
# ll.add(
#     ForAll(
#         [Delta, Gamma, B],
#         Implies(
#             entails(comma(Delta, comma(em(B), em(B))), Gamma),
#             entails(comma(Delta, em(B)), Gamma),
#         ),
#     )
# )

# # !D
# ll.add(
#     ForAll(
#         [Delta, Gamma, B],
#         Implies(
#             entails(comma(Delta, B), Gamma),
#             entails(comma(Delta, em(B)), Gamma),
#         ),
#     )
# )

# # !R
# ll.add(
#     ForAll(
#         [Delta, Gamma, B],
#         Implies(
#             entails(em(Delta), comma(B, qm(Gamma))),
#             entails(em(Delta), comma(em(B), qm(Gamma))),
#         ),
#     )
# )

# ll.add(Not(entails(tensor(x,one), x))) # unsat
# ll.add(Not(entails(one, lpop(x, x)))) # unsat
# ll.add(Not(entails(x, star(x)))) # unsat
def mkStr(l):
    if len(l) == 0:
        return one
    return tensor(l[0], mkStr(l[1:]))
    # return tensor(mkStr(n - 1) ,tensor(x,y))

s = mkStr([x,y] * 6)
print(s)

# ll.add(Not(entails(star(x), star(oplus(x, y)))))
# ll.add(Not(entails(oplus(x,y), oplus(oplus(z, x), y))))
ll.add(Not(entails(s, star(tensor(x, y))))) # unsat up to n = 25
# ll.add(Not(entails(mkStr(4), star(tensor(x, y)))))
# ll.add(Not(entails(tensor(tensor(x , y), tensor(y,z)), tensor(x, tensor(y, tensor(y,z))))))
# ll.add(Not(entails(star(tensor(x,x)), star(x))))
print(ll.check())
