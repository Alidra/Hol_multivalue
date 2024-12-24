require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1097740_term_abbrevs;
opaque symbol lem1097740 [A B] : Prf (= (@MAP A B) (term0 A B)) ≔ @MAP_def A B;
