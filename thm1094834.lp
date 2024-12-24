require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1094834_term_abbrevs;
opaque symbol lem1094834 [A] : Prf (= (@HD A) (term0 A)) ≔ @HD_def A;
