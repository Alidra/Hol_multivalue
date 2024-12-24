require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1046237_term_abbrevs;
opaque symbol lem1046237 (a : El num) (d : El num) (b : El num) (c : El num) : Prf (= (term0 a b c d) (= (term1 a b c d) (term2 a d b c))) ≔ REFL (term0 a b c d);
