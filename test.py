from z3 import *

# Intuitionisitc propositional logic tests

# TODO these aren't split into R and X,
# so the formatting might need to change based on Bryan's code

neg = lambda a : Implies(a , False)
dbl_neg = lambda a : Implies(a , Implies(Implies(a , False), False))
dbl_neg_gen = lambda a , b : Implies(a , Implies(Implies(a , b), b))
lem = lambda a : Or(a , neg(a))

neg_neg_to_dbl_neg = lambda a : Implies(neg(neg(a)), dbl_neg(a))
dbl_neg_to_neg_neg = lambda a : Implies(dbl_neg(a), neg(neg(a)))
trpl_neg = lambda a : neg(dbl_neg(a))

dbl_neg_lem = lambda a : dbl_neg(lem(a))
dbl_neg_gen_lem = lambda a , b : Implies(Implies(Or(a, Implies(a , b)), b), b)

# coproduct univ prop
case_fwd = lambda a, b : Implies(Implies(Or(a, b) , c), And(Implies(a, c), Implies(b , c)))
case_rev = lambda a, b : Implies(And(Implies(a, c), Implies(b , c)), Implies(Or(a, b) , c))

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
