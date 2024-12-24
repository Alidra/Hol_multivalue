require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.REAL_NEG_0_term_abbrevs;
require open hol-light.thm1361604_spec;
require open hol-light.thm1362040_spec;
opaque symbol lem1362041 : Prf (= term0 term1) ≔ EQ_MP (@lem1361604) (@lem1362040);
