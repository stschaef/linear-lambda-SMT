from z3 import *
from warnings import warn

def clausify(A):
    """
    Transforms the formula A into canonical form.
    
    Args:
        A (z3.BoolRef): A propositional formula.

    Returns:
        z3.BoolRef: Formula A transformed into canonical form.
    """
    # Ensure A is in the form (B -> q)
    A, goal = format_proof_goal(A)
    
    # Recursively transform
    R, X = [], []
    transform(A, R, X)

    # Reconstruct formula
    return Implies(And(R + X), goal)


def format_proof_goal(A):
    """
    Ensures that A is in the form (B -> q), where q is an atom. If not, convert to (A -> q) -> q.

    Args:
        A (z3.BoolRef): A propositional formula.

    Returns:
        tuple[z3.BoolRef, z3.BoolRef]: The antecedent and the proof goal.
    """
    if is_implies(A) and is_atom(A.children()[1]):
        return tuple(A.children())
    else:
        goal = FreshBool()
        return Implies(A, goal), goal


def transform(formula, R, X):
    """
    Recursively constructs flat and implication clauses.

    Args:
        A (z3.BoolRef): The formula to transform.
        R (list[z3.BoolRef]): The list of flat clauses to populate.
        X (list[z3.BoolRef]): The list of implication clauses to populate.
    """
    # base cases
    if is_flat_clause(formula):
        R.append(formula)
        return

    if is_implication_clause(formula):
        X.append(formula)
        return
    
    if not is_implies(formula):
        raise Exception("Not an implication clause: " + str(formula))
    
    left, right = formula.children()

    # rewrite negation as A -> False
    if is_not(left):
        left = Implies(left.children()[0], False)
    if is_not(right):
        right = Implies(right.children()[0], False)

    # (A || B || ..) -> C     ->      c -> C, A -> c, B -> c, ..
    if is_or(left):
        # atomize right side with a -> A
        if not is_atom(right):
            atom = FreshBool()
            transform(Implies(atom, right), R, X)
            right = atom
        
        for A in left.children():
            transform(Implies(A, right), R, X)

    # a -> (A && B && ..)     ->      a -> A, a -> B, ..
    elif is_and(right):
        for A in right.children():
            transform(Implies(left, A), R, X)

    # A -> (B -> C)     ->      (A && B) -> C
    elif is_implies(right):
        B, C = right.children()
        transform(Implies(And(left, B), C), R, X)

    # A -> (.. || B || ..)      ->      A -> (.. || b || ..), b -> B
    elif is_or(right):
        new_consequent = []
        for B in right.children():
            if not is_atom(B):
                b = FreshBool()
                transform(Implies(b, B), R, X)
                new_consequent.append(b)
            else:
                new_consequent.append(B)
        transform(Implies(left, Or(new_consequent)), R, X)

    # (.. && A && ..) -> B      ->      (.. && a && ..) -> B, A -> a
    elif is_and(left):
        new_antecedent = []
        for A in left.children():
            if not is_atom(A):
                a = FreshBool()
                transform(Implies(A, a), R, X)
                new_antecedent.append(a)
            else:
                new_antecedent.append(A)
        transform(Implies(And(new_antecedent), right), R, X)

    # (A -> B) -> C     ->      (a -> b) -> c, a -> A, B -> b, c -> C
    elif is_implies(left):
        A, B = left.children()

        if not is_atom(A):
            a = FreshBool()
            transform(Implies(a, A), R, X)
            A = a
        if not is_atom(B):
            b = FreshBool()
            transform(Implies(b, B), R, X)
            B = b
        if not is_atom(right):
            c = FreshBool()
            transform(Implies(c, right), R, X)
            right = c
        
        transform(Implies(Implies(A, B), right), R, X)

    else:
        raise Exception("No transformation rule applies: " + str(formula))


def is_atom(A):
    """Returns true if A is an atom."""
    return not A.children()


def is_flat_clause(A):
    """Returns true if A is in the form (a_1 && .. && a_n) -> (b_1 || .. || b_m), where m, n > 0."""
    if not is_implies(A):
        warn("is_flat_clause() was called with a non-implication formula")
        return False
    
    left, right = A.children()

    if not ((is_and(left) or is_atom(left)) and (is_or(right) or is_atom(right))):
        return False

    for a in left.children():
        if not is_atom(a):
            return False
    for b in right.children():
        if not is_atom(b):
            return False
    
    return True


def is_implication_clause(A):
    """Returns true if A is in the form (a -> b) -> c."""
    if not is_implies(A):
        warn("is_implication_clause() was called with a non-implication formula")
        return False

    ab, c = A.children()
    
    if not is_implies(ab) or not is_atom(c):
        return False
    
    a, b = ab.children()
    return is_atom(a) and is_atom(b)


if __name__ == "__main__":
    p, q, r, s, t = FreshBool(), FreshBool(), FreshBool(), FreshBool(), FreshBool()
    formula = Implies(Implies(Or(p, q), r), And(s, t))
    clausified = clausify(formula)
    print(clausified)