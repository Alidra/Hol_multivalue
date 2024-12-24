require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1111523 [A] : Prf (∀ (λ h : El A, (∀ (λ t : El (list A), (¬ (= ((@CONS A) h t) (@NIL A)))))));
