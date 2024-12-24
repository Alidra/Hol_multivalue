require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1200321 [A] : Prf (∧ (= ((@BUTLAST A) (@NIL A)) (@NIL A)) (∧ (∀ (λ a : El A, (= ((@BUTLAST A) ((@CONS A) a (@NIL A))) (@NIL A)))) (∀ (λ a : El A, (∀ (λ h : El A, (∀ (λ t : El (list A), (= ((@BUTLAST A) ((@CONS A) a ((@CONS A) h t))) ((@CONS A) a ((@BUTLAST A) ((@CONS A) h t))))))))))));
