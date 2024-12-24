require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1069764_term_abbrevs;
opaque symbol lem1069764 [A] : Prf (= (@NONE A) (term0 A)) ≔ @NONE_def A;
