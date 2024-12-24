require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1095357_term_abbrevs;
opaque symbol lem1095357 [A] : Prf (= (@TL A) (term0 A)) ≔ @TL_def A;
