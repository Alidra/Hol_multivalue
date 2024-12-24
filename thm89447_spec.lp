require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem89447 : Prf (= <= ((@ε (fun (prod num num) (fun num (fun num bool)))) (λ <=' : El (fun (prod num num) (fun num (fun num bool))), (∀ (λ _2241 : El (prod num num), (∧ (∀ (λ m : El num, (= (<=' _2241 m (NUMERAL _0)) (= m (NUMERAL _0))))) (∀ (λ m : El num, (∀ (λ n : El num, (= (<=' _2241 m (SUC n)) (∨ (= m (SUC n)) (<=' _2241 m n))))))))))) ((@̦‚ num num) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 _0))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 _0))))))))));
