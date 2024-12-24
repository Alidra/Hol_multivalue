require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1491_term_abbrevs;
require open hol-light.thm32_spec;
opaque symbol lem1491 : Prf (= term0 (= (¬ T) F)) ≔ (@lem32 (¬ T) F);
