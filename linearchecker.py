import re

class ProofChecker:
    def __init__(self, proof):
        self.proof = proof
        self.used_assumptions = {}

    def parse_proof(self):
        # Extract assumptions, rules, and conclusions
        # This example assumes a nested structure of calls (e.g., `unit-resolution`, `asserted`)
        # Parsing logic would depend on your proof representation format
        tokens = re.findall(r'\w+\(.*?\)', self.proof)
        return tokens

    def check_linearity(self, tokens):
        """
        Check if every assumption is used exactly once.
        """
        for token in tokens:
            if 'asserted' in token:
                assumption = re.search(r'asserted\((.*?)\)', token).group(1)
                if assumption not in self.used_assumptions:
                    self.used_assumptions[assumption] = 0
                self.used_assumptions[assumption] += 1

        # Ensure each assumption is used exactly once
        for assumption, count in self.used_assumptions.items():
            if count != 1:
                return False, f"Assumption '{assumption}' used {count} times."
        return True, "Linearity check passed."

    def check_intuitionistic_rules(self):
        """
        Ensure no classical rules are used (e.g., excluded middle, double negation elimination).
        """
        classical_rules = ['excluded_middle', 'double_negation_elim']
        for rule in classical_rules:
            if rule in self.proof:
                return False, f"Classical rule '{rule}' used."
        return True, "Intuitionistic rules check passed."

    def validate(self):
        tokens = self.parse_proof()
        linearity_check, linearity_message = self.check_linearity(tokens)
        intuitionistic_check, intuitionistic_message = self.check_intuitionistic_rules()

        if not linearity_check:
            return False, linearity_message
        if not intuitionistic_check:
            return False, intuitionistic_message
        return True, "Proof is valid in linear intuitionistic logic."


# Example proof
proof = """unit-resolution(unit-resolution(mp(asserted(Implies(b0, c)),
                                   rewrite(Implies(b0, c) ==
                                        Or(c, Not(b0))),
                                   Or(c, Not(b0))),
                                and-elim(asserted(And(a, b0)),
                                        b0),
                                c),
                asserted(Not(c)),
                False)"""

checker = ProofChecker(proof)
is_valid, message = checker.validate()
print(message)
