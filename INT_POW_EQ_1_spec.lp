require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2307928 : Prf (∀ (λ x : El int, (∀ (λ n : El num, (= (= (int_pow x n) (int_of_num (NUMERAL (BIT1 _0)))) (∨ (∧ (= (int_abs x) (int_of_num (NUMERAL (BIT1 _0)))) (⇒ (int_lt x (int_of_num (NUMERAL _0))) (EVEN n))) (= n (NUMERAL _0))))))));
