require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem21751 (t : El bool) : Prf (∧ (= (∨ F t) t) (∧ (= (∨ t F) t) (= (∨ t t) t)));
