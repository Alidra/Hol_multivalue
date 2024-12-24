require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5459080 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (⇒ (<= m (+ n (NUMERAL (BIT1 _0)))) (= (… m (+ n p)) ((@UNION num) (… m n) (… (+ n (NUMERAL (BIT1 _0))) (+ n p)))))))))));
