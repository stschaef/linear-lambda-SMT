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

from z3 import *
from test import *

set_option(proof=True)
# Create a new solver instance with proof generation enabled
s = Solver()

def satProve(solver, A, q):
    """
    Attempts to prove the goal 'q' from the assumptions 'A' using the flat clauses in solver 'solver'.
    Returns ('Yes', assumptions_used, proof) if 'q' can be proved, or ('No', model) if not.
    """
    # Create a new solver instance to avoid state conflicts
    # s = SolverFor("QF_UF")  # Use an appropriate logic
    # s.set(proof=True)  # Enable proof generation
    s.add(solver.assertions())
    # Combine assumptions and the negation of the goal
    assumptions = list(A) + [Not(q)]
    res = s.check(assumptions)
    if res == unsat:
        proof = s.proof()
        core = s.unsat_core()
        # Remove Not(q) from the core to get the assumptions actually used
        core_without_q = [a for a in core if not (eq(a, Not(q)))]
        return ('Yes', core_without_q, proof)
    elif res == sat:
        M = s.model()
        return ('No', M)
    else:
        return ('Unknown', None)

def intuitCheck(solver, X, M):
    """
    Checks whether the classical model 'M' corresponds to an intuitionistic model.
    If not, adds a new flat clause to 'solver' and returns False. Otherwise, returns True.
    """
    for (a, b, c) in X:
        # Evaluate a, b, c in the model M
        if(type(a)!=bool): 
            a_val = M.evaluate(a)
        else:
            a_val = a
        if(type(b)!=bool): 
            b_val = M.evaluate(b)
        else:
            b_val = b
        if(type(c)!=bool): 
            c_val = M.evaluate(c)
        else:
            c_val = c
        # Proceed only if a, b, c are not assigned True in M
        if is_true(a_val) or is_true(b_val) or is_true(c_val):
            continue  # Skip this implication clause
        else:
            # Build the set of assumptions A = M ∪ {a}
            A = set()
            for d in M.decls():
                val = M[d]
                if is_true(val):
                    A.add(d())
            A.add(a)
            # Remove the current implication clause from X
            X_minus_i = X.copy()
            X_minus_i.remove((a, b, c))
            # Recursively attempt to prove 'b' from 'A'
            result = intuitProve(solver, X_minus_i, A, b)
            if result[0] == 'Yes':
                A_prime = result[1]
                # Remove 'a' from A_prime to get assumptions used
                assumptions_used = set(A_prime)
                assumptions_used.discard(a)
                # Create new flat clause (assumptions_used) → c
                if len(assumptions_used) == 0:
                    new_clause = c  # Implies(True, c) simplifies to c
                else:
                    new_clause = Implies(And(*assumptions_used), c)
                solver.add(new_clause)
                return False  # Indicate that the model was inadequate
    return True  # The model corresponds to an intuitionistic model

def intuitProve(solver, X, A, q):
    """
    Main loop that attempts to prove 'q' from 'A' using solver 'solver' and handles
    counterexamples via 'intuitCheck'.
    """
    while True:
        result = satProve(solver, A, q)
        if result[0] == 'Yes':
            A_prime = result[1]
            proof = result[2]
            return ('Yes', A_prime, proof)
        elif result[0] == 'No':
            M = result[1]
            if intuitCheck(solver, X, M):
                return ('No', M)
            # Else, continue the loop with updated 'solver'
        else:
            return ('Unknown', None)

def prove(R, X, q):
    """
    Top-level procedure that initializes the solver, adds clauses, and starts the proof.
    """
    
    # Add all flat clauses to the solver
    for r in R:
        s.add(r)
    # For each implication clause (a → b) → c, add the flat clause b → c
    for (a, b, c) in X:
        s.add(Implies(b, c))
    # Start the intuitionistic proving process
    result = intuitProve(s, X, set(), q)
    return result

# Example usage
if __name__ == "__main__":
    # Define atoms
    a = Bool('a')
    b = Bool('b')
    b0 = Bool('b0')
    b1 = Bool('b1')
    b2 = Bool('b2')
    b3 = Bool('b3')
    b4 = Bool('b4')
    b5 = Bool('b5')
    b6 = Bool('b6')
    b7 = Bool('b7')
    b8 = Bool('b8')
    b9 = Bool('b9')
    b10 = Bool('b10')
    c = Bool('c')
    d = Bool('d')
    e = Bool('e')
    f = Bool('f')
    p = Bool('p')  # a → b
    q_atom = Bool('q_atom')  # b → c
    r = Bool('r')  # a → c
    s_atom = Bool('s')  # Goal atom

    # Flat clauses R
    R = [
        Implies(And(b6, b7), False),  
        Implies(And(b8, b0), b9),
        Implies(And(b9, b10), False),
    ]

    # Implication clauses X
    X = [   
        (b0, False, b7),
        (b0, False, b10),
        (b6, b8, b5)
    ]

    # The goal is to prove 's'
    q = b5

    # Run the prove function
    result = prove(R, X, q)

    # Output the result and the proof
    if result[0] == 'Yes':
        print("The formula is intuitionistically provable.")
        proof = result[2]
        print("Proof:")
        print(proof)
    elif result[0] == 'No':
        print(result[1])
        print("The formula is not intuitionistically provable.")
    else:
        print("The result is unknown.")
