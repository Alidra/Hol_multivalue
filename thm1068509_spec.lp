require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1068509 [A B] : Prf (= (@OUTL A B) ((@ε (fun (prod num (prod num (prod num num))) (fun (Sum A B) A))) (λ OUTL' : El (fun (prod num (prod num (prod num num))) (fun (Sum A B) A)), (∀ (λ _17486 : El (prod num (prod num (prod num num))), (∀ (λ x : El A, (= (OUTL' _17486 ((@INL A B) x)) x)))))) ((@̦‚ num (prod num (prod num num))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) ((@̦‚ num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) ((@̦‚ num num) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))))))));
