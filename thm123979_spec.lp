require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem123979 : Prf ((λ EVEN' : El (fun (prod num (prod num (prod num num))) (fun num bool)), (∀ (λ _2603 : El (prod num (prod num (prod num num))), (∧ (= (EVEN' _2603 (NUMERAL _0)) T) (∀ (λ n : El num, (= (EVEN' _2603 (SUC n)) (¬ (EVEN' _2603 n))))))))) ((@ε (fun (prod num (prod num (prod num num))) (fun num bool))) (λ EVEN' : El (fun (prod num (prod num (prod num num))) (fun num bool)), (∀ (λ _2603 : El (prod num (prod num (prod num num))), (∧ (= (EVEN' _2603 (NUMERAL _0)) T) (∀ (λ n : El num, (= (EVEN' _2603 (SUC n)) (¬ (EVEN' _2603 n)))))))))));
