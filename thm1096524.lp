require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1096524_term_abbrevs;
opaque symbol lem1096524 [A] (l : El (list A)) (x : El A) : Prf (= (term0 A l x) (= (term1 A x l) (term2 A l x))) ≔ REFL (term0 A l x);
