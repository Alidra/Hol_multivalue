require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1843 (t : El bool) : Prf (∧ (= (∧ t T) t) (∧ (= (∧ F t) F) (∧ (= (∧ t F) F) (= (∧ t t) t))));
