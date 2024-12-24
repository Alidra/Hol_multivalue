require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem16464 (t : El bool) : Prf (∧ (= (= F t) (¬ t)) (= (= t F) (¬ t)));
