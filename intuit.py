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

def intuitPR(solver, X, A, q):
    result = satProve(solver, A, q)
    if result[0] == 'Yes':
        A_prime = result[1]
        proof = result[2]
        return ('Yes', A_prime, proof)
    elif result[0] == 'No':
        M = result[1]
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
                A_old = A
                A.add(a)
                # Remove the current implication clause from X
                X_minus_i = X.copy()
                X_minus_i.remove((a, b, c))

                result = intuitPR(solver, X_minus_i, A, b)

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
                    return intuitPR(solver, X, A_old, q)
        return ('No', M)


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
    # result = intuitProve(s, X, set(), q)
    result = intuitPR(s, X, set(), q)
    return result

class Impl:
    def __init__(self, ant, conseq):
        self.ant = ant
        self.conseq = conseq
        self.normalize()

    def normalize(self):
        self.ant = [ p for p in self.ant if (p != [] and p != set())]

    def __str__(self):
        return self.__repr__()

    def __repr__(self):
        return ",".join([ str(p) for p in self.ant ]) + " => " + str(self.conseq)

def flatten(xss):
    ans = []
    for xs in xss:
        if type(xs) != list and type(xs) != set:
            ans.append(xs)
        else:
            for x in xs:
                ans.append(x)
    return ans


class Proof:
    def __init__(self, premises, conclusion, rule):
        self.premises = premises
        self.conclusion = conclusion
        self.rule = rule
        self.normalize()

    def normalize(self):
        if (type(self.premises) == list) :
            self.premises = [ p for p in self.premises if (p != [] and p != set())]

    def str_help(self, indent=0):
        def ind(n):
            return n * "  "
        s = ind(indent) + "Proof\n"
        s += ind(indent + 1) + "Conclusion:\n"
        s += ind(indent + 2) + str(self.conclusion) + '\n'
        s += ind(indent + 1) + "Rule: " + self.rule + '\n'
        # premises are a collection of proofs
        if type(self.premises) == list or type(self.premises) == type:
            for p in flatten(self.premises):
                s += ind(indent + 1)+ "Premise: " + "\n"
                if type(p) == BoolRef :
                    s += ind(indent + 2) + str(p) + '\n'
                else:
                    s += p.str_help(indent + 1) + '\n'
        else: # premise is a proof
            s += ind(indent + 1) + "Premise: " + "\n"
            s += self.premises.str_help(indent + 1) + '\n'
        return s

    def __str__(self):
        return self.str_help()

    def __repr__(self):
        return f"premises: {self.premises};conclusion: {self.conclusion};rule: {self.rule}"



def LJTSat(R, X, A, q, r, solver, R_0, X_0, q_0, Rs):
    """
    An extension of IntuitProve/IntuitPR that returns proofs

    return in format,

    "Proof" , proof tree, assumptions R, assumptions A
    """
    result = satProve(solver, A, q)
    if result[0] == 'Yes':
        A_prime = result[1]
        pf = Proof(
            Proof([Rs, A_prime], q, "|-cpl"),
            Impl([Rs, X, A_prime], q),
            "cpl"
        )
        return "Proof", pf, Rs, A_prime
    elif result[0] == 'No':

        M = result[1]
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
                A_old = A
                A.add(a)
                # Remove the current implication clause from X
                X_minus_i = X.copy()
                X_minus_i.remove((a, b, c))

                R_new = R | {Implies(b, c)}

                r_new = r + [(a,b,c)]

                result_ = LJTSat(R_new, X_minus_i, A, b, r_new, solver, R_0, X_0, q_0, Rs)
                if result_ == None:
                    # Theta[(a,b,c)] = result_
                    continue
                else:
                    A_prime = result_[3]
                    # Remove 'a' from A_prime to get assumptions used
                    assumptions_used = set(A_prime)
                    assumptions_used.discard(a)

                    new_clause = None # phi tilde
                    # Create new flat clause (assumptions_used) → c
                    if len(assumptions_used) == 0:
                        new_clause = c  # Implies(True, c) simplifies to c
                    else:
                        new_clause = Implies(And(*assumptions_used), c)

                    solver.add(new_clause)
                    Rs.add(new_clause)

                    R_new_ = R | {new_clause}
                    nextResult = LJTSat(R_new_, X, A, q, r, solver, R_0, X_0, q_0, Rs)

                    if nextResult == None:
                        return None
                    else :
                        pf = Proof(
                            [Proof(result_[1], Impl([R , result_[2], Implies(b,c), X_minus_i, result_[3]], b), ""),
                             Proof(result_[1], Impl([R , nextResult[2], new_clause, X, nextResult[3]], q), "")],
                            Impl([R, result_[2], nextResult[2], nextResult[3]], q),
                            "ljt"
                        )
                        return "Proof", pf, \
                           (result_[2] | nextResult[2]), nextResult[3]
        return None

def LJTSatMain(R_0, X_0, q_0):
    R_0 = set(R_0)
    Rs = set()
    for r in R_0:
        s.add(r)
        Rs.add(r)
    for (a, b, c) in X_0:
        s.add(Implies(b, c))
        Rs.add(Implies(b,c))
    result = LJTSat(R_0, X_0, set(), q_0, [], s, R_0, X_0, q_0, Rs)
    if result == None:
        return None
    else:
        _, D, R, A = result
        R_proofs = [ Proof([R_0, X_0], r, "|-ipl") for r in R ]
        prems = R_proofs + [Proof([D] , Impl([R_0, R, X_0], q_0), "")]
        ans = Proof(prems, Impl([R_0, X_0], q_0), "cut")
        return ans

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
    b11 = Bool('b11')
    b12 = Bool('b12')
    b13 = Bool('b13')
    b14 = Bool('b14')
    b15 = Bool('b15')
    b16 = Bool('b16')
    b17 = Bool('b17')
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
        Implies(And(b12, b0), False)
    ]

    # Implication clauses X
    X = [   (b12,False,b11),
         (b0,b11,b10)
    ]

    # The goal is to prove 's'
    q = b10

    # Run the prove function
    # result = prove(R, X, q)
    result = LJTSatMain(set(R), X, q)

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
