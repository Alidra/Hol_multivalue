require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.REAL_SGN_0_term_abbrevs;
require open hol-light.thm1710179_spec;
require open hol-light.thm1710422_spec;
opaque symbol lem1710423 : Prf (= term0 term1) ≔ EQ_MP (@lem1710179) (@lem1710422);
