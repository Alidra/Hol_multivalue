require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1638435 : Prf (∀ (λ n : El num, (∀ (λ x : El real, (⇒ (∧ (¬ (= n (NUMERAL _0))) (real_lt (real_of_num (NUMERAL (BIT1 _0))) x)) (real_lt (real_of_num (NUMERAL (BIT1 _0))) (real_pow x n)))))));
