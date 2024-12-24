require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem146068 : Prf (= FACT ((@ε (fun (prod num (prod num (prod num num))) (fun num num))) (λ FACT' : El (fun (prod num (prod num (prod num num))) (fun num num)), (∀ (λ _2944 : El (prod num (prod num (prod num num))), (∧ (= (FACT' _2944 (NUMERAL _0)) (NUMERAL (BIT1 _0))) (∀ (λ n : El num, (= (FACT' _2944 (SUC n)) (* (SUC n) (FACT' _2944 n))))))))) ((@̦‚ num (prod num (prod num num))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) ((@̦‚ num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) ((@̦‚ num num) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))))));
