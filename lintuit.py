## Importing the z3 module
from z3 import *
## Declarations
ll = Solver ()
F = DeclareSort("F")
entails = Function ("entails ", F , F , BoolSort ())
tensor = Function ("tensor ", F , F , F )
lpop = Function ("lollipop ", F , F , F )
x, y, z, Gamma, Delta, B, B1, B2, zero, Top = Consts("x y z Gamma Delta B B1 B2 zero Top", F)

## Given rules
ll . add ( ForAll ([ x ] , entails (x , x ))) # (i)
ll . add ( ForAll ([ x ,y , z ], entails ( tensor (x ,y ) , z ) == entails (y , lpop (x , z )))) # (c)


### Additive Rules ###
oplus = Function("oplus", F, F, F)
amp = Function("with", F, F, F)

# 0L
ll.add(ForAll([Delta, Gamma], entails(tensor(Delta, zero), Gamma)))

# TR
ll.add(ForAll([Delta, Gamma], entails(Delta, tensor(Top, Gamma))))

# &L(i = 1,2)
ll.add(
    ForAll([Delta, B1, B2, Gamma],
           Implies(
               Or(entails(tensor(Delta, B1), Gamma),
                  entails(tensor(Delta, B2), Gamma)),
               entails(tensor(Delta, amp(B1, B2)), Gamma)
           ))
)

# &R
ll.add(
    ForAll([Delta, B1, B2, Gamma],
           Implies(
               And(entails(Delta, tensor(B1, Gamma)),
                   entails(Delta, tensor(B2, Gamma))),
               entails(Delta, tensor(amp(B1, B2), Gamma))
           ))
)

# (+)L

ll.add(
    ForAll([Delta, B1, B2, Gamma],
           Implies(
               And(entails(tensor(Delta, B1), Gamma), 
                   entails(tensor(Delta, B2), Gamma)),
               entails(tensor(Delta, oplus(B1, B2)), Gamma)
           ))
)

# (+)R(i = 1,2)
ll.add(
    ForAll([Delta, B1, B2, Gamma],
           Implies(
               Or(entails(Delta, tensor(B1, Gamma)),
                  entails(Delta, tensor(B2, Gamma))),
               entails(Delta, tensor(oplus(B1, B2), Gamma))
           ))
)

### Exponential Rules ###
em = Function("em", F, F)
qm = Function("qm", F, F)

# !W
ll.add(
    ForAll([Delta, Gamma, B],
           Implies(
               entails(Delta, Gamma),
               entails(tensor(Delta, em(B)), Gamma)
           ))
)

# !C
ll.add(
    ForAll([Delta, Gamma, B],
           Implies(
               entails(tensor(Delta, tensor(em(B), em(B))), Gamma),
               entails(tensor(Delta, em(B)), Gamma)
           ))
)

# !D
ll.add(
    ForAll([Delta, Gamma, B],
           Implies(
               entails(tensor(Delta, B), Gamma),
               entails(tensor(Delta, em(B)), Gamma)
           ))
)

# !R
ll.add(
    ForAll([Delta, Gamma, B],
           Implies(
               entails(em(Delta), tensor(B, qm(Gamma))),
               entails(em(Delta), tensor(em(B), qm(Gamma)))
           ))
)

# ?W
ll.add(
    ForAll([Delta, Gamma, B],
           Implies(
               entails(Delta, Gamma),
               entails(Delta, tensor(qm(B), Gamma))
           ))
)

# ?C
ll.add(
    ForAll([Delta, Gamma, B],
           Implies(
               entails(Delta, tensor(tensor(qm(B), qm(B)), Gamma)),
               entails(Delta, tensor(qm(B), Gamma))
           ))
)

# ?D
ll.add(
    ForAll([Delta, Gamma, B],
           Implies(
               entails(Delta, tensor(B, Gamma)),
               entails(Delta, tensor(qm(B), Gamma))
           ))
)

# ?L
ll.add(
    ForAll([Delta, Gamma, B],
           Implies(
               entails(tensor(em(Delta), B), qm(Gamma)),
               entails(tensor(em(Delta), qm(B)), qm(Gamma))
           ))
)