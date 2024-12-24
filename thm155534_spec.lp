require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem155534 : Prf (= DIV ((@ε (fun (prod num (prod num num)) (fun num (fun num num)))) (λ q : El (fun (prod num (prod num num)) (fun num (fun num num))), (∀ (λ _3086 : El (prod num (prod num num)), (∃ (λ r : El (fun num (fun num num)), (∀ (λ m : El num, (∀ (λ n : El num, ((@COND bool) (= n (NUMERAL _0)) (∧ (= (q _3086 m n) (NUMERAL _0)) (= (r m n) m)) (∧ (= m (+ (* (q _3086 m n) n) (r m n))) (< (r m n) n)))))))))))) ((@̦‚ num (prod num num)) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) ((@̦‚ num num) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))))));
