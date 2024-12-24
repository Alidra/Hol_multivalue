require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1099685 [_25287] : Prf ((λ NULL' : El (fun (prod num (prod num (prod num num))) (fun (list _25287) bool)), (∀ (λ _17966 : El (prod num (prod num (prod num num))), (∧ (= (NULL' _17966 (@NIL _25287)) T) (∀ (λ h : El _25287, (∀ (λ t : El (list _25287), (= (NULL' _17966 ((@CONS _25287) h t)) F))))))))) ((@ε (fun (prod num (prod num (prod num num))) (fun (list _25287) bool))) (λ NULL' : El (fun (prod num (prod num (prod num num))) (fun (list _25287) bool)), (∀ (λ _17966 : El (prod num (prod num (prod num num))), (∧ (= (NULL' _17966 (@NIL _25287)) T) (∀ (λ h : El _25287, (∀ (λ t : El (list _25287), (= (NULL' _17966 ((@CONS _25287) h t)) F)))))))))));
