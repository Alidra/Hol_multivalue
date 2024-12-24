require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem155860 : Prf (= MOD ((@ε (fun (prod num (prod num num)) (fun num (fun num num)))) (λ r : El (fun (prod num (prod num num)) (fun num (fun num num))), (∀ (λ _3087 : El (prod num (prod num num)), (∀ (λ m : El num, (∀ (λ n : El num, ((@COND bool) (= n (NUMERAL _0)) (∧ (= (DIV m n) (NUMERAL _0)) (= (r _3087 m n) m)) (∧ (= m (+ (* (DIV m n) n) (r _3087 m n))) (< (r _3087 m n) n)))))))))) ((@̦‚ num (prod num num)) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) ((@̦‚ num num) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0))))))))))));
