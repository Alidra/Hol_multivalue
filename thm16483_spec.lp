require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem16483 (t : El bool) : Prf (∧ (= (∨ t T) T) (∧ (= (∨ F t) t) (∧ (= (∨ t F) t) (= (∨ t t) t))));
