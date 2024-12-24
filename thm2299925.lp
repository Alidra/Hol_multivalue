require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2299925_term_abbrevs;
opaque symbol lem2299925 (x : El int) (y : El int) : Prf (= (term0 x y) (= (term1 x y) (int_gt x y))) ≔ REFL (term0 x y);
