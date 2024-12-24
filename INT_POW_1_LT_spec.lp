require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2307722 : Prf (∀ (λ n : El num, (∀ (λ x : El int, (⇒ (∧ (¬ (= n (NUMERAL _0))) (∧ (int_le (int_of_num (NUMERAL _0)) x) (int_lt x (int_of_num (NUMERAL (BIT1 _0)))))) (int_lt (int_pow x n) (int_of_num (NUMERAL (BIT1 _0)))))))));
