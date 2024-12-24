require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1094488 [A] : Prf ((λ HD' : El (fun (prod num num) (fun (list A) A)), (∀ (λ _17927 : El (prod num num), (∀ (λ t : El (list A), (∀ (λ h : El A, (= (HD' _17927 ((@CONS A) h t)) h)))))))) ((@ε (fun (prod num num) (fun (list A) A))) (λ HD' : El (fun (prod num num) (fun (list A) A)), (∀ (λ _17927 : El (prod num num), (∀ (λ t : El (list A), (∀ (λ h : El A, (= (HD' _17927 ((@CONS A) h t)) h))))))))));
