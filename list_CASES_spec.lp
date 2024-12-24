require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1114169 [A] : Prf (∀ (λ l : El (list A), (∨ (= l (@NIL A)) (∃ (λ h : El A, (∃ (λ t : El (list A), (= l ((@CONS A) h t)))))))));
