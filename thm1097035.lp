require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1097035_term_abbrevs;
opaque symbol lem1097035 [A] : Prf (= (@LENGTH A) (term0 A)) ≔ @LENGTH_def A;
