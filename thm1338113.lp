require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1338113_term_abbrevs;
opaque symbol lem1338113 (x : El (prod hreal hreal)) (y : El (prod hreal hreal)) : Prf (= (term0 x y) (= (treal_eq x y) (= (term1 x) (term1 y)))) ≔ REFL (term0 x y);
