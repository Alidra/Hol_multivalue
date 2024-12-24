require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem16495 (t : El bool) : Prf (∧ (= (∧ F t) F) (∧ (= (∧ t F) F) (= (∧ t t) t)));
