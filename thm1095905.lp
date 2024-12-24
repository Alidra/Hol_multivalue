require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1095905_term_abbrevs;
opaque symbol lem1095905 [A] : Prf (= (@APPEND A) (term0 A)) ≔ @APPEND_def A;
