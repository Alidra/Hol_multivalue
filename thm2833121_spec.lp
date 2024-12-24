require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2833121 (a : El int) (d : El int) (b : El int) : Prf (= ((λ b' : El int, (= (int_divides d (int_gcd ((@̦‚ int int) a b'))) (∧ (int_divides d a) (int_divides d b')))) b) (= (int_divides d (int_gcd ((@̦‚ int int) a b))) (∧ (int_divides d a) (int_divides d b))));
