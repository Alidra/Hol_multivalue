require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem124577 : Prf (= ODD ((@ε (fun (prod num (prod num num)) (fun num bool))) (λ ODD' : El (fun (prod num (prod num num)) (fun num bool)), (∀ (λ _2607 : El (prod num (prod num num)), (∧ (= (ODD' _2607 (NUMERAL _0)) F) (∀ (λ n : El num, (= (ODD' _2607 (SUC n)) (¬ (ODD' _2607 n))))))))) ((@̦‚ num (prod num num)) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) ((@̦‚ num num) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0))))))))))));
