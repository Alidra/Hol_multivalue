require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2833121_term_abbrevs;
opaque symbol lem2833121 (a : El int) (d : El int) (b : El int) : Prf (= (term0 a d b) (= (term1 d a b) (term2 a d b))) ≔ REFL (term0 a d b);
