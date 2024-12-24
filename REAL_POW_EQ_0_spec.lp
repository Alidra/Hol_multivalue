require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1630283 : Prf (∀ (λ x : El real, (∀ (λ n : El num, (= (= (real_pow x n) (real_of_num (NUMERAL _0))) (∧ (= x (real_of_num (NUMERAL _0))) (¬ (= n (NUMERAL _0)))))))));
