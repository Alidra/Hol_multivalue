require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2406288_term_abbrevs;
opaque symbol lem2406288 (x : El int) (y : El int) : Prf (= (term0 x y) (= (int_sub x y) (term1 x y))) ≔ REFL (term0 x y);
