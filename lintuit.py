## Importing the z3 module
from z3 import *
## Declarations
ll = Solver ()
F = DeclareSort("F")
entails = Function ("entails ", F , F , BoolSort ())
tensor = Function ("tensor ", F , F , F )
lpop = Function ("lollipop ", F , F , F )
x , y , z = Consts ("x y z", F )

## Given rules
ll . add ( ForAll ([ x ] , entails (x , x ))) # (i)
ll . add ( ForAll ([ x ,y , z ], entails ( tensor (x ,y ) , z ) == entails (y , lpop (x , z )))) # (c)