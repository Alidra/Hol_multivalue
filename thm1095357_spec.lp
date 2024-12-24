require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1095357 [A] : Prf (= (@TL A) ((@ε (fun (prod num num) (fun (list A) (list A)))) (λ TL' : El (fun (prod num num) (fun (list A) (list A))), (∀ (λ _17931 : El (prod num num), (∀ (λ h : El A, (∀ (λ t : El (list A), (= (TL' _17931 ((@CONS A) h t)) t)))))))) ((@̦‚ num num) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))))));
