require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1106559 [_25594] : Prf (∧ (∀ (λ P : El (fun _25594 bool), (= ((@FILTER _25594) P (@NIL _25594)) (@NIL _25594)))) (∀ (λ h : El _25594, (∀ (λ P : El (fun _25594 bool), (∀ (λ t : El (list _25594), (= ((@FILTER _25594) P ((@CONS _25594) h t)) ((@COND (list _25594)) (P h) ((@CONS _25594) h ((@FILTER _25594) P t)) ((@FILTER _25594) P t))))))))));
