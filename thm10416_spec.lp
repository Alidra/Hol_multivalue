require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem10416 (t : El bool) : Prf ((λ t' : El bool, (= (¬ (¬ t')) t')) t);
