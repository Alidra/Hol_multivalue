require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7332366 : Prf (∀ (λ x : El real, (∀ (λ n : El num, (⇒ (<= (NUMERAL (BIT1 _0)) n) (= (real_sub (real_pow x n) (real_of_num (NUMERAL (BIT1 _0)))) (real_mul (real_sub x (real_of_num (NUMERAL (BIT1 _0)))) ((@sum num) (… (NUMERAL _0) (- n (NUMERAL (BIT1 _0)))) (λ i : El num, (real_pow x i))))))))));
