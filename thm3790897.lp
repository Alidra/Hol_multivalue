require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3790897_term_abbrevs;
opaque symbol lem3790897 [A B] : Prf (= (@FINREC A B) (term0 A B)) ≔ @FINREC_def A B;
