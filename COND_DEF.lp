require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.COND_DEF_term_abbrevs;
opaque symbol lem12296 [A] : Prf (= (@COND A) (term0 A)) ≔ @COND_def A;
