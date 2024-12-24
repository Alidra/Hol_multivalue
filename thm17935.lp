require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm17935_term_abbrevs;
opaque symbol lem17935 [A] (y : El A) (x : El A) : Prf (= (term0 A x y) (= (= x y) (= y x))) ≔ REFL (term0 A x y);
