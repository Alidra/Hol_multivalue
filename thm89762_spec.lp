require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem89762 : Prf ((λ <' : El (fun num (fun num (fun num bool))), (∀ (λ _2248 : El num, (∧ (∀ (λ m : El num, (= (<' _2248 m (NUMERAL _0)) F))) (∀ (λ m : El num, (∀ (λ n : El num, (= (<' _2248 m (SUC n)) (∨ (= m n) (<' _2248 m n))))))))))) ((@ε (fun num (fun num (fun num bool)))) (λ <' : El (fun num (fun num (fun num bool))), (∀ (λ _2248 : El num, (∧ (∀ (λ m : El num, (= (<' _2248 m (NUMERAL _0)) F))) (∀ (λ m : El num, (∀ (λ n : El num, (= (<' _2248 m (SUC n)) (∨ (= m n) (<' _2248 m n)))))))))))));
