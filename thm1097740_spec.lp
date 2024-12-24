require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1097740 [A B] : Prf (= (@MAP A B) ((@ε (fun (prod num (prod num num)) (fun (fun A B) (fun (list A) (list B))))) (λ MAP' : El (fun (prod num (prod num num)) (fun (fun A B) (fun (list A) (list B)))), (∀ (λ _17950 : El (prod num (prod num num)), (∧ (∀ (λ f : El (fun A B), (= (MAP' _17950 f (@NIL A)) (@NIL B)))) (∀ (λ f : El (fun A B), (∀ (λ h : El A, (∀ (λ t : El (list A), (= (MAP' _17950 f ((@CONS A) h t)) ((@CONS B) (f h) (MAP' _17950 f t))))))))))))) ((@̦‚ num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) ((@̦‚ num num) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))))));
