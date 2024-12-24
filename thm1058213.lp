require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1058213_term_abbrevs;
opaque symbol lem1058213 [A] : Prf (= (@ZBOT A) (term0 A)) ≔ @ZBOT_def A;
