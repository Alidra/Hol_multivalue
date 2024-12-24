require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm6401229_term_abbrevs;
opaque symbol lem6401229 [A K] : Prf (= (@iterato A K) (term0 A K)) ≔ @iterato_def A K;
