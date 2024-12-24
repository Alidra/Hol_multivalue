require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem76680 : Prf ((λ PRE' : El (fun (prod num (prod num num)) (fun num num)), (∀ (λ _2151 : El (prod num (prod num num)), (∧ (= (PRE' _2151 (NUMERAL _0)) (NUMERAL _0)) (∀ (λ n : El num, (= (PRE' _2151 (SUC n)) n))))))) ((@ε (fun (prod num (prod num num)) (fun num num))) (λ PRE' : El (fun (prod num (prod num num)) (fun num num)), (∀ (λ _2151 : El (prod num (prod num num)), (∧ (= (PRE' _2151 (NUMERAL _0)) (NUMERAL _0)) (∀ (λ n : El num, (= (PRE' _2151 (SUC n)) n)))))))));
