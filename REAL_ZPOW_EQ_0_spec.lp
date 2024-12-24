require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3179842 : Prf (∀ (λ x : El real, (∀ (λ n : El int, (= (= (real_zpow x n) (real_of_num (NUMERAL _0))) (∧ (= x (real_of_num (NUMERAL _0))) (¬ (= n (int_of_num (NUMERAL _0))))))))));
