require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1073523 [A] : Prf (∀ (λ a0' : El A, (∀ (λ a1' : El (list A), (¬ (= (@NIL A) ((@CONS A) a0' a1')))))));
