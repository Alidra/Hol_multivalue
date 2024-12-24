require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1070110_term_abbrevs;
opaque symbol lem1070110 [A] : Prf (= (@SOME A) (term0 A)) ≔ @SOME_def A;
