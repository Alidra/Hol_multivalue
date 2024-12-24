require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7931479 [A] (a : El (finite_sum A A)) (a' : El (finite_sum A A)) : Prf ((λ a'' : El (finite_sum A A), (= (= ((@mktybit0 A) a) ((@mktybit0 A) a'')) (= a a''))) a');
