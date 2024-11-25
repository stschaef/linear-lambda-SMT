def And(*args):
    raise NotImplementedError


def Or(*args):
    raise NotImplementedError


def Not(arg):
    raise NotImplementedError


def Implies(left, right):
    raise NotImplementedError


def is_and(formula):
    raise NotImplementedError


def is_or(formula):
    raise NotImplementedError


def is_not(formula):
    raise NotImplementedError


def is_implies(formula):
    raise NotImplementedError


def is_atom(formula):
    return not get_children(formula)


def get_children(formula):
    raise NotImplementedError


def FreshBool():
    raise NotImplementedError


class Solver(object):
    def __init__(self):
        raise NotImplementedError

    def add(self, clause):
        raise NotImplementedError

    def check(self):
        raise NotImplementedError