require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1810_term_abbrevs;
opaque symbol lem1810 [A B] (f : El (fun A B)) (y : El A) : Prf (= (term0 A B f y) (= (term1 A B f y) (f y))) ≔ REFL (term0 A B f y);
