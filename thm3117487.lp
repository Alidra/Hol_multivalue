require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3117487_term_abbrevs;
opaque symbol lem3117487 (a : El num) (b : El num) : Prf (= (term0 a b) (= (term1 a b) (term2 a b))) ≔ REFL (term0 a b);
