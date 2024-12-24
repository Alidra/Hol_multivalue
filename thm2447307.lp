require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2447307_term_abbrevs;
opaque symbol lem2447307 (x : El int) (y : El int) (n : El int) : Prf (= (term0 x y n) (= (term1 x y n) (term2 x y n))) ≔ REFL (term0 x y n);
