require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1097800 [A B] : Prf (∧ (∀ (λ f : El (fun A B), (= ((@MAP A B) f (@NIL A)) (@NIL B)))) (∀ (λ f : El (fun A B), (∀ (λ h : El A, (∀ (λ t : El (list A), (= ((@MAP A B) f ((@CONS A) h t)) ((@CONS B) (f h) ((@MAP A B) f t))))))))));
