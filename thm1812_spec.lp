require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1812 [A] (t : El bool) : Prf ((λ t' : El bool, (= (∃ (λ x : El A, t')) t')) t);
