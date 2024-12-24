require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3211663_term_abbrevs;
opaque symbol lem3211663 [A] (s : El (type686 A)) (x : El A) : Prf (= (term0 A s x) (= (term1 A x s) (term2 A s x))) ≔ REFL (term0 A s x);
