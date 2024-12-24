require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7931480_term_abbrevs;
opaque symbol lem7931480 [A] (a : El (finite_sum A A)) (a' : El (finite_sum A A)) : Prf (= (term0 A a a') (= (= ((@mktybit0 A) a) ((@mktybit0 A) a')) (= a a'))) ≔ REFL (term0 A a a');
