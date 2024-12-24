require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2306211 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (int_lt (int_of_num (NUMERAL _0)) (int_mul x y)) (∨ (∧ (int_lt (int_of_num (NUMERAL _0)) x) (int_lt (int_of_num (NUMERAL _0)) y)) (∧ (int_lt x (int_of_num (NUMERAL _0))) (int_lt y (int_of_num (NUMERAL _0))))))))));
