require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem124194 : Prf (= EVEN ((@ε (fun (prod num (prod num (prod num num))) (fun num bool))) (λ EVEN' : El (fun (prod num (prod num (prod num num))) (fun num bool)), (∀ (λ _2603 : El (prod num (prod num (prod num num))), (∧ (= (EVEN' _2603 (NUMERAL _0)) T) (∀ (λ n : El num, (= (EVEN' _2603 (SUC n)) (¬ (EVEN' _2603 n))))))))) ((@̦‚ num (prod num (prod num num))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) ((@̦‚ num (prod num num)) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) ((@̦‚ num num) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))))))));
