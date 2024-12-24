require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1098310_term_abbrevs;
opaque symbol lem1098310 [A] : Prf (= (@LAST A) (term0 A)) ≔ @LAST_def A;
