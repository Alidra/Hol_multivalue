require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.IMP_CONJ_term_abbrevs;
require open hol-light.thm885_spec;
require open hol-light.thm886_spec;
opaque symbol lem887 (p : El bool) (q : El bool) (r : El bool) : Prf (= (term0 p q r) (term1 p q r)) ≔ EQ_MP (@lem886 p q r) (@lem885 p q r);
