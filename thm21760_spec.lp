require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem21760 (t : El bool) : Prf (∧ (= (∧ T t) t) (∧ (= (∧ t T) t) (∧ (= (∧ F t) F) (∧ (= (∧ t F) F) (= (∧ t t) t)))));
