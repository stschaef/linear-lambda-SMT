from z3 import *
import clausify
import intuit
import unittest

# Intuitionisitc propositional logic tests

# TODO these aren't split into R and X,
# so the formatting might need to change based on Bryan's code

neg = lambda a : Implies(a , False)
dbl_neg_gen = lambda a , b : Implies(a , Implies(Implies(a , b), b))
dbl_neg = lambda a : neg(neg(a))
dbl_neg_in = lambda a : Implies(a , Implies(Implies(a , False), False))
dbl_neg_elim = lambda a : Implies(Implies(Implies(a , False), False), a)
lem = lambda a : Or(a , neg(a))

neg_neg_to_dbl_neg = lambda a : Implies(neg(neg(a)), dbl_neg(a))
dbl_neg_to_neg_neg = lambda a : Implies(dbl_neg(a), neg(neg(a)))
trpl_neg = lambda a : neg(dbl_neg(a))

dbl_neg_lem = lambda a : dbl_neg(lem(a))
dbl_neg_gen_lem = lambda a , b : Implies(Implies(Or(a, Implies(a , b)), b), b)

# coproduct univ prop
case_fwd = lambda a, b, c : Implies(Implies(Or(a, b) , c), And(Implies(a, c), Implies(b , c)))
case_rev = lambda a, b, c : Implies(And(Implies(a, c), Implies(b , c)), Implies(Or(a, b) , c))

prod_univ_prop_fwd = lambda a, b, c : Implies(Implies(a, And(b , c)), And(Implies(a , c), Implies(a, c)))
prod_univ_prop_rev = lambda a, b, c : Implies(And(Implies(a , c), Implies(b, c)), Implies(a, And(b , c)))

curry = lambda a, b, c : Implies(Implies(a, Implies(b, c)), Implies(And(a , b), c))
uncurry = lambda a, b, c : Implies(Implies(And(a , b), c), Implies(a, Implies(b, c)))

pierce = lambda a, b : Implies(Implies(Implies(a , b), a), a)

pierce_to_lem = lambda a , b : Implies(lem(a), pierce(a, b))
lem_to_pierce = lambda a , b : Implies(pierce(a, b), lem(a))

explode = lambda a : Implies(False, a)

triple_neg_to_neg = lambda a : Implies(trpl_neg(a), neg(a))

demorgan_fwd = lambda a, b : Implies(And(neg(a), neg(b)), neg(Or(a, b)))
demorgan_rev = lambda a, b : Implies(neg(Or(a,b)), And(neg(a), neg(b)))

demorgan2_fwd = lambda a, b : Implies(Or(neg(a), neg(b)), neg(And(a, b)))
demorgan2_rev = lambda a, b : Implies(neg(And(a,b)), Or(neg(a), neg(b))) # not provable

contra_neg = lambda a , b : Implies(Implies(a , neg(b)), Implies(b, neg(a)))
contra = lambda a , b : Implies(Implies(a , b), Implies(neg(b), neg(a))) # shouldn't be provable

weak = lambda a , b : Implies(a , Implies(b , a))

terminal = lambda a : Implies(a , True)

# larger tests of incidental complexity
test1 = lambda a, b, c, d, e, f, g : \
  Implies(
      And(
          Implies(Implies(a, b), c),
          And(
              Implies(c , Implies(Implies(d ,e) ,f)),
              And(
                  Implies(Or(a, b), b),
                  And(
                      Implies(d , e),
                      neg(f)
                  )
              )
          )
      ),
      g
  )

test2 = lambda a, b, c, d, e : \
  Implies(
      And(
          trpl_neg(a),
          And(
              Implies(Implies(b, c), a),
              Implies(b, And(d, c))
          )
      ),
      e
  )

big_curry = lambda a, b, c, d, e : \
  Implies(
      And(
          a,
          And(
              b,
              And(c, d)
          )
      ),
      e
  )

lambdas = \
  [
    ["neg", neg, False],
    ["dbl_neg_in", dbl_neg_in, True],
    ["dbl_neg_elim", dbl_neg_elim, False],
    ["dbl_neg_gen", dbl_neg_gen, False],
    ["lem", lem, False],
    # ["neg_neg_to_dbl_neg", neg_neg_to_dbl_neg, True],
    # ["dbl_neg_to_neg_neg", dbl_neg_to_neg_neg, True],
    # ["trpl_neg", trpl_neg, False],
    # ["dbl_neg_lem", dbl_neg_lem, True],
    # ["dbl_neg_gen_lem", dbl_neg_gen_lem, True],
    # ["case_fwd", case_fwd, True],
    # ["case_rev", case_rev, True],
    # ["prod_univ_prop_fwd", prod_univ_prop_fwd, True],
    # ["prod_univ_prop_rev", prod_univ_prop_rev, True],
    # ["curry", curry, True],
    # ["uncurry", uncurry, True],
    # ["pierce", pierce, False],
    # ["pierce_to_lem", pierce_to_lem, True],
    # ["lem_to_pierce", lem_to_pierce, True],
    # ["explode", explode, True],
    # ["triple_neg_to_neg", triple_neg_to_neg, True],
    # ["demorgan_fwd", demorgan_fwd, True],
    # ["demorgan_rev", demorgan_rev, True],
    # ["demorgan2_fwd", demorgan2_fwd, True],
    # ["demorgan2_rev", demorgan2_rev, False],
    # ["contra_neg", contra_neg, True],
    # ["contra", contra, False],
    # ["weak", weak, True],
    # ["terminal", terminal, True],
    # ["test1", test1, True],
    # ["test2", test2, True],
    # ["big_curry", big_curry, True]
  ]

class ClausifyTests(unittest.TestCase):
    pass

class  ProvabilityTests(unittest.TestCase):
    pass

def ClausifyTestGen(f):
    def test(self):
        self.assertEqual(str(clausify.isEquivToClausified(f)), "unsat")
    return test

def ProvabilityTestGen(R, X, goal, b):
    def test(self):
        self.assertEqual(
            intuit.prove(
                R,
                clausify.formatX(X),
                goal)[0],
            'Yes' if b else 'No')
    return test

if __name__ == '__main__':
    # formula = clausify.instantiateLambda(dbl_neg_in)
    # R, X, goal = clausify.RXGoal(formula)
    # print(R, X, goal)
    # print(intuit.prove(R, clausify.formatX(X), goal))

    for t in lambdas:
        # clausify_test_name = 'test_equiv_clausify_%s' % t[0]
        # clausify_test = ClausifyTestGen(t[1])
        # setattr(ClausifyTests, clausify_test_name, clausify_test)

        provability_test_name = 'test_%s' % t[0]
        formula = clausify.instantiateLambda(t[1])
        R, X, goal = clausify.RXGoal(formula)
        provability_test = ProvabilityTestGen(R, X, goal, t[2])
        setattr(ProvabilityTests, provability_test_name, provability_test)
    unittest.main()
