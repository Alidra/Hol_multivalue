require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1068987 [A B] : Prf (= (@OUTR A B) ((@ε (fun (prod num (prod num (prod num num))) (fun (Sum A B) B))) (λ OUTR' : El (fun (prod num (prod num (prod num num))) (fun (Sum A B) B)), (∀ (λ _17488 : El (prod num (prod num (prod num num))), (∀ (λ y : El B, (= (OUTR' _17488 ((@INR A B) y)) y)))))) ((@̦‚ num (prod num (prod num num))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) ((@̦‚ num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) ((@̦‚ num num) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))))));
