require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1067668_term_abbrevs;
opaque symbol lem1067668 [A B] : Prf (= (@INR A B) (term0 A B)) ≔ @INR_def A B;
