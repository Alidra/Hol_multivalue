require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.INT_NEG_0_term_abbrevs;
require open hol-light.REAL_NEG_0_spec;
require open hol-light.thm2306330_spec;
opaque symbol lem2306331 : Prf (= term0 term1) ≔ EQ_MP (@lem2306330) (@lem1362041);
