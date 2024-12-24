require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.IMP_CONJ_ALT_term_abbrevs;
require open hol-light.thm951_spec;
require open hol-light.thm952_spec;
opaque symbol lem953 (q : El bool) (p : El bool) (r : El bool) : Prf (= (term0 p q r) (term1 q p r)) ≔ EQ_MP (@lem952 q p r) (@lem951 p q r);
