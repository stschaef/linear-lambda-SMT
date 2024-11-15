from z3 import *
from test import *

s = Solver()
def satProve(s, A, q):
    """
    Attempts to prove the goal 'q' from the assumptions 'A' using the flat clauses in solver 's'.
    Returns ('Yes', assumptions_used) if 'q' can be proved, or ('No', model) if not.
    """
    s.set(unsat_core=True)
    # Combine assumptions and the negation of the goal
    assumptions = list(A) + [Not(q)]
    res = s.check(assumptions)
    if res == unsat:
        core = s.unsat_core()
        # Remove Not(q) from the core to get the assumptions actually used
        core_without_q = [a for a in core if not (eq(a, Not(q)))]
        return ('Yes', core_without_q)
    elif res == sat:
        M = s.model()
        return ('No', M)
    else:
        return ('Unknown', None)

def intuitCheck(s, X, M):
    """
    Checks whether the classical model 'M' corresponds to an intuitionistic model.
    If not, adds a new flat clause to 's' and returns False. Otherwise, returns True.
    """
    for (a, b, c) in X:
        # Evaluate a, b, c in the model M
        a_val = M.evaluate(a)
        b_val = M.evaluate(b)
        c_val = M.evaluate(c)
        # Proceed only if a, b, c are not assigned True in M
        if is_true(a_val) or is_true(b_val) or is_true(c_val):
            continue  # Skip this implication clause
        else:
            # Build the set of assumptions A = M \cup {a}
            A = set()
            print(M)
            for d in M.decls():
                val = M[d]
                if is_true(val):
                    A.add(d())
                # A.add(d())
            A.add(a)
            # Remove the current implication clause from X
            X_minus_i = X.copy()
            X_minus_i.remove((a, b, c))
            # Recursively attempt to prove 'b' from 'A'
            print(b)
            print(A)
            result = intuitProve(s, X_minus_i, A, b)
            if result[0] == 'Yes':
                A_prime = result[1]
                # Remove 'a' from A_prime to get assumptions used
                assumptions_used = set(A_prime)
                assumptions_used.discard(a)
                # Create new flat clause (assumptions_used) \to c
                if len(assumptions_used) == 0:
                    new_clause = c  # Implies(True, c) simplifies to c
                else:
                    new_clause = Implies(And(*assumptions_used), c)
                print(new_clause)
                s.add(new_clause)
                return False  # Indicate that the model was inadequate
    return True  # The model corresponds to an intuitionistic model

def intuitProve(s, X, A, q):
    """
    Main loop that attempts to prove 'q' from 'A' using solver 's' and handles
    counterexamples via 'intuitCheck'.
    """
    while True:
        result = satProve(s, A, q)
        if result[0] == 'Yes':
            A_prime = result[1]
            return ('Yes', A_prime)
        elif result[0] == 'No':
            M = result[1]
            if intuitCheck(s, X, M):
                return ('No', M)
            # Else, continue the loop with updated 's'
        else:
            return ('Unknown', None)

def prove(R, X, q):
    """
    Top-level procedure that initializes the solver, adds clauses, and starts the proof.
    """
    
    # s.set(unsat_core=True)
    # Add all flat clauses to the solver
    for r in R:
        s.add(r)
    # For each implication clause (a \to b) \to c, add the flat clause b \to c
    for (a, b, c) in X:
        s.add(Implies(b, c))
    print(s)
    # Start the intuitionistic proving process
    result = intuitProve(s, X, set(), q)
    return result

# Helper function to create atoms (propositional variables)
def Atom(name):
    return Bool(name)


if __name__ == "__main__":
    # Define atoms
    a = Bool('a')
    b = Bool('b')
    c = Bool('c')
    d = Bool('d')
    e = Bool('e')
    f = Bool('f')
    g = Bool('g')

    p = Bool('p')

    q_atom = Bool('q_atom')  
    r = Bool('r')
    s_atom = Bool('s')  

    # Flat clauses R
    R = [
      dbl_neg(a)
    ]

    # Implication clauses X
    X = [
    ]

    # The goal is to prove 's'
    q = c

    # Run the prove function
    result = prove(R, X, q)

    # Output the result
    if result[0] == 'Yes':
        print("The formula is intuitionistically provable.")
    elif result[0] == 'No':
        print("The formula is not intuitionistically provable.")
    else:
        print("The result is unknown.")
