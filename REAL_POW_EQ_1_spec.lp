require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1657725 : Prf (∀ (λ x : El real, (∀ (λ n : El num, (= (= (real_pow x n) (real_of_num (NUMERAL (BIT1 _0)))) (∨ (∧ (= (real_abs x) (real_of_num (NUMERAL (BIT1 _0)))) (⇒ (real_lt x (real_of_num (NUMERAL _0))) (EVEN n))) (= n (NUMERAL _0))))))));
