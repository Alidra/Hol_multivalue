require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2403542 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (= (int_lt (rem m n) n) (∨ (int_lt (int_of_num (NUMERAL _0)) n) (∧ (= n (int_of_num (NUMERAL _0))) (int_lt m (int_of_num (NUMERAL _0))))))))));
