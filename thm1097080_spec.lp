require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1097080 [A] : Prf (∧ (= ((@LENGTH A) (@NIL A)) (NUMERAL _0)) (∀ (λ h : El A, (∀ (λ t : El (list A), (= ((@LENGTH A) ((@CONS A) h t)) (SUC ((@LENGTH A) t))))))));
