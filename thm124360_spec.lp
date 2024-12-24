require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem124360 : Prf ((λ ODD' : El (fun (prod num (prod num num)) (fun num bool)), (∀ (λ _2607 : El (prod num (prod num num)), (∧ (= (ODD' _2607 (NUMERAL _0)) F) (∀ (λ n : El num, (= (ODD' _2607 (SUC n)) (¬ (ODD' _2607 n))))))))) ((@ε (fun (prod num (prod num num)) (fun num bool))) (λ ODD' : El (fun (prod num (prod num num)) (fun num bool)), (∀ (λ _2607 : El (prod num (prod num num)), (∧ (= (ODD' _2607 (NUMERAL _0)) F) (∀ (λ n : El num, (= (ODD' _2607 (SUC n)) (¬ (ODD' _2607 n)))))))))));
