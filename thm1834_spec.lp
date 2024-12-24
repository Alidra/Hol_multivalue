require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1834 (t : El bool) : Prf (∧ (= (∨ t F) t) (= (∨ t t) t));
