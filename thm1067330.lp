require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1067330_term_abbrevs;
opaque symbol lem1067330 [A B] : Prf (= (@INL A B) (term0 A B)) ≔ @INL_def A B;
