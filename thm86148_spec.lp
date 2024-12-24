require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem86148 : Prf (= EXP ((@ε (fun (prod num (prod num num)) (fun num (fun num num)))) (λ EXP' : El (fun (prod num (prod num num)) (fun num (fun num num))), (∀ (λ _2224 : El (prod num (prod num num)), (∧ (∀ (λ m : El num, (= (EXP' _2224 m (NUMERAL _0)) (NUMERAL (BIT1 _0))))) (∀ (λ m : El num, (∀ (λ n : El num, (= (EXP' _2224 m (SUC n)) (* m (EXP' _2224 m n))))))))))) ((@̦‚ num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) ((@̦‚ num num) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))))));
