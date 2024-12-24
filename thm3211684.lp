require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3211684_term_abbrevs;
opaque symbol lem3211684 [A] (s : El (fun A bool)) (x : El A) (y : El A) : Prf (= (term0 A s x y) (= (term1 A x s y) (term2 A s x y))) ≔ REFL (term0 A s x y);
