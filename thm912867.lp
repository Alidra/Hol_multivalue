require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm912867_term_abbrevs;
require open hol-light.thm715609_spec;
require open hol-light.thm715612_spec;
opaque symbol lem912867 : Prf (= term0 term1) ≔ TRANS (@lem715609) (@lem715612);
