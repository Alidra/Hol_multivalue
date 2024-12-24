require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm587_term_abbrevs;
require open hol-light.thm585_spec;
require open hol-light.thm586_spec;
opaque symbol lem587 (p : El bool) (q : El bool) (r : El bool) : Prf (= (term0 p q r) (term1 p q r)) ≔ EQ_MP (@lem586 p q r) (@lem585 p q r);
