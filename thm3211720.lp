require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3211720_term_abbrevs;
opaque symbol lem3211720 [A] (s : El (fun A bool)) (x : El A) (t : El (fun A bool)) : Prf (= (term0 A s t x) (= (term1 A x s t) (term2 A s x t))) ≔ REFL (term0 A s t x);
