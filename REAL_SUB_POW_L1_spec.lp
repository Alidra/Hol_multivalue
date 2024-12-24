require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7335682 : Prf (∀ (λ x : El real, (∀ (λ n : El num, (⇒ (<= (NUMERAL (BIT1 _0)) n) (= (real_sub (real_of_num (NUMERAL (BIT1 _0))) (real_pow x n)) (real_mul (real_sub (real_of_num (NUMERAL (BIT1 _0))) x) ((@sum num) (… (NUMERAL _0) (- n (NUMERAL (BIT1 _0)))) (λ i : El num, (real_pow x i))))))))));
