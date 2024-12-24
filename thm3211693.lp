require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3211693_term_abbrevs;
opaque symbol lem3211693 [A] (y : El A) (x : El A) (s : El (fun A bool)) : Prf (= (term0 A y x s) (= (term1 A x y s) (term2 A y x s))) ≔ REFL (term0 A y x s);
