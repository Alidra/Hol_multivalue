require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7332274 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ n : El num, (⇒ (<= (NUMERAL (BIT1 _0)) n) (= (real_sub (real_pow x n) (real_pow y n)) (real_mul (real_sub x y) ((@sum num) (… (NUMERAL _0) (- n (NUMERAL (BIT1 _0)))) (λ i : El num, (real_mul (real_pow x i) (real_pow y (- (- n (NUMERAL (BIT1 _0))) i))))))))))))));
