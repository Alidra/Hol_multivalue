require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1068509_term_abbrevs;
opaque symbol lem1068509 [A B] : Prf (= (@OUTL A B) (term0 A B)) ≔ @OUTL_def A B;
