require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3187402_term_abbrevs;
opaque symbol lem3187402 [A] : Prf (= (@UNIV A) (term0 A)) ≔ @UNIV_def A;
