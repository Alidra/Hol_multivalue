require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1831 (t : El bool) : Prf (∧ (= (∨ T t) T) (∧ (= (∨ t T) T) (∧ (= (∨ F t) t) (∧ (= (∨ t F) t) (= (∨ t t) t)))));
