require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1071681_term_abbrevs;
opaque symbol lem1071681 [A] : Prf (= (@CONS A) (term0 A)) ≔ @CONS_def A;
