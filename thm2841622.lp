require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2841622_term_abbrevs;
opaque symbol lem2841622 (x : El int) (y : El int) : Prf (= (term0 x y) (= (= x y) (= (real_of_int x) (real_of_int y)))) ≔ REFL (term0 x y);
