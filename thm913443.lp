require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm913443_term_abbrevs;
require open hol-light.thm759283_spec;
require open hol-light.thm759298_spec;
opaque symbol lem913443 : Prf (= term0 term1) ≔ TRANS (@lem759283) (@lem759298);
