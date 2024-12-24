require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2307872 : Prf (∀ (λ x : El int, (∀ (λ n : El num, (= (= (int_pow x n) (int_of_num (NUMERAL _0))) (∧ (= x (int_of_num (NUMERAL _0))) (¬ (= n (NUMERAL _0)))))))));
