require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem57694 [A] (t : El A) : Prf ((λ t' : El A, (= ((@LET_END A) t') t')) t);
