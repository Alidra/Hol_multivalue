require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem145847 : Prf ((λ FACT' : El (fun (prod num (prod num (prod num num))) (fun num num)), (∀ (λ _2944 : El (prod num (prod num (prod num num))), (∧ (= (FACT' _2944 (NUMERAL _0)) (NUMERAL (BIT1 _0))) (∀ (λ n : El num, (= (FACT' _2944 (SUC n)) (* (SUC n) (FACT' _2944 n))))))))) ((@ε (fun (prod num (prod num (prod num num))) (fun num num))) (λ FACT' : El (fun (prod num (prod num (prod num num))) (fun num num)), (∀ (λ _2944 : El (prod num (prod num (prod num num))), (∧ (= (FACT' _2944 (NUMERAL _0)) (NUMERAL (BIT1 _0))) (∀ (λ n : El num, (= (FACT' _2944 (SUC n)) (* (SUC n) (FACT' _2944 n)))))))))));
