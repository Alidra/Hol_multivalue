require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2626069 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (= (= (div m n) (int_of_num (NUMERAL _0))) (∨ (= n (int_of_num (NUMERAL _0))) (∧ (int_le (int_of_num (NUMERAL _0)) m) (int_lt m (int_abs n)))))))));
