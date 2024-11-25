import z3

def And(*args):
    return z3.And(*args)


def Or(*args):
    return z3.Or(*args)


def Not(arg):
    return z3.Not(arg)


def Implies(left, right):
    return z3.Implies(left, right)


def is_and(formula):
    return z3.is_and(formula)


def is_or(formula):
    return z3.is_or(formula)


def is_not(formula):
    return z3.is_not(formula)


def is_implies(formula):
    return z3.is_implies(formula)


def is_atom(formula):
    return not get_children(formula)


def get_children(formula):
    return formula.children()


def FreshBool():
    return z3.FreshBool()


class Solver(z3.Solver):
    def __init__(self):
        super().__init__()

    def add(self, clause):
        super().add(clause)

    def check(self):
        super().check()