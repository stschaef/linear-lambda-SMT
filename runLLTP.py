import re
from z3 import *

## Declarations
ll = Solver()
F = DeclareSort("F")

entails = Function("entails", F, F, BoolSort())
tensor = Function("tensor", F, F, F)
lpop = Function("lpop", F, F, F)
oplus = Function("oplus", F, F, F)
amp = Function("with", F, F, F)
star = Function("*", F, F)
dual = Function("dual", F, F)
par = Function("par", F, F,)

# Variables
x, y, z, w = Consts('x y z w', F)
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
# ll.add(ForAll([x], entails(tensor(star(x), x), star(x))))

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
)  # (c)
## Multiplicative Rules

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
em = Function("em", F, F)
# qm = Function("qm", F, F)

ll.add(ForAll([x], entails(x, em(x))))
ll.add(ForAll([x], entails(em(x), tensor(em(x), em(x)))))
ll.add(ForAll([x], entails(tensor(em(x), em(x)), em(x))))

# !W
# ll.add(
#     ForAll(
#         [Delta, B],
#         Implies(
#             entails(Delta, Gamma),
#             entails(tensor(Delta, em(B)), Gamma),
#         ),
#     )
# )

# !C
# ll.add(
#     ForAll(
#         [Delta, Gamma, B],
#         Implies(
#             entails(tensor(Delta, tensor(em(B), em(B))), Gamma),
#             entails(tensor(Delta, em(B)), Gamma),
#         ),
#     )
# )

# # !D
# ll.add(
#     ForAll(
#         [Delta, Gamma, B],
#         Implies(
#             entails(tensor(Delta, B), Gamma),
#             entails(tensor(Delta, em(B)), Gamma),
#         ),
#     )
# )

# !R
# ll.add(
#     ForAll(
#         [Delta, Gamma, B],
#         Implies(
#             entails(em(Delta), tensor(B, qm(Gamma))),
#             entails(em(Delta), tensor(em(B), qm(Gamma))),
#         ),
#     )
# )



# Parsing routines from before
variables = {}

def get_variable(name):
    if name not in variables:
        variables[name] = Const(name, F)
    return variables[name]

def extract_formula_parts(tptp_line):
    pattern = r"fof\s*\(\s*([a-zA-Z0-9_]+)\s*,\s*([a-zA-Z0-9_]+)\s*,\s*(.*?)\)\s*\."
    m = re.match(pattern, tptp_line.strip())
    if m:
        name = m.group(1)
        role = m.group(2)
        formula_str = m.group(3).strip()
        return name, role, formula_str
    else:
        return None, None, None

def tokenize(formula_str):
    formula_str = formula_str.replace('(', ' ( ').replace(')', ' ) ')
    formula_str = formula_str.replace('-o', ' -o ')
    for op in ['!', '?', '&', '*', '+', '|', '^']:
        formula_str = formula_str.replace(op, f' {op} ')
    tokens = formula_str.split()
    return tokens

class Parser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0

    def peek(self):
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return None

    def consume(self, token=None):
        if token and self.peek() != token:
            raise ValueError(f"Expected '{token}' but got '{self.peek()}'")
        t = self.peek()
        self.pos += 1
        return t

    def parse_formula(self):
        left = self.parse_unary()
        while True:
            nxt = self.peek()
            if nxt in ['*', '&', '|', '+', '-o']:
                op = self.consume()
                right = self.parse_unary()
                left = self.apply_binary(op, left, right)
            else:
                break
        return left

    def parse_unary(self):
        node = self.parse_atomic()
        while self.peek() == '^':
            self.consume('^')
            node = dual(node)  
        return node

    def parse_atomic(self):
        nxt = self.peek()

        if nxt == '(':
            self.consume('(')
            f = self.parse_formula()
            self.consume(')')
            return f
        elif nxt == '!':
            self.consume('!')
            f = self.parse_atomic()
            return em(f)
        elif nxt == '?':
            self.consume('?')
            f = self.parse_atomic()
            qm = Function("qm", F, F)
            return qm(f)
        else:
            t = self.consume()
            if t == 'bot':
                bottom = Const('bottom', F)
                return bottom
            elif t == 'top':
                return Top
            elif t == '0':
                zero = Const('0', F)
                return zero
            elif t == '1':
                return one
            else:
                return get_variable(t)

    def apply_binary(self, op, left, right):
        if op == '*':
            return tensor(left, right)
        elif op == '&':
            return amp(left, right)  
        elif op == '|':
            return par(left, right)
        elif op == '+':
            return oplus(left, right)
        elif op == '-o':
            return lpop(left, right)
        else:
            raise ValueError("Unknown binary operator: "+op)

def parse_tptp_to_z3py(formula_str):
    tokens = tokenize(formula_str)
    parser = Parser(tokens)
    expr = parser.parse_formula()
    if parser.peek() is not None:
        raise ValueError("Extra tokens after parsing.")
    return expr

def parse_tptp_file(filename):
    with open(filename, 'r') as f:
        lines = f.readlines()
    results = {}
    for line in lines:
        line = line.strip()
        if not line or line.startswith('%'):
            continue
        name, role, formula = extract_formula_parts(line)
        if name is not None:
            expr = parse_tptp_to_z3py(formula)
            results[name] = (role, expr)
    return results

def combine_axioms_and_conjecture(results):
    # Separate axioms and conjecture
    axioms = [expr for (role, expr) in results.values() if role == "axiom"]
    conjectures = [expr for (role, expr) in results.values() if role == "conjecture"]

    if not conjectures:
        raise ValueError("No conjecture found.")
    conjecture = conjectures[0]

    # Combine axioms with amp as logical "and"
    if not axioms:
        all_axioms = one  # if no axioms, use I as a neutral element
    else:
        all_axioms = axioms[0]
        for ax in axioms[1:]:
            all_axioms = amp(all_axioms, ax)

    return all_axioms, conjecture

# Example usage:
# Assume the input file is "KLE001+1.p"
# containing:
#
# %--------------------------------------------------------------------------
# % File     : KLE001+1 : ...
# % ...
# fof(con1, conjecture, !((!(a) -o a))). 
# %--------------------------------------------------------------------------
#
filename = "lltp/ILL/KLE-01/KLE002+1.p"
results = parse_tptp_file(filename)
all_axioms, conjecture = combine_axioms_and_conjecture(results)

# Create entailment
entailment_expr = entails(all_axioms, conjecture)
print(entailment_expr)
# Add the negation of the entailment to the solver
ll.add(Not(entailment_expr))

# Check satisfiability
print(ll.check())
if ll.check() == sat:
    print(ll.model())
