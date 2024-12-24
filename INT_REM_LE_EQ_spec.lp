require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2658979 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (= (int_le (rem m n) m) (∨ (= n (int_of_num (NUMERAL _0))) (int_le (int_of_num (NUMERAL _0)) m)))))));
