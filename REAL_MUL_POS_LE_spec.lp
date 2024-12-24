require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1628374 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (= (real_le (real_of_num (NUMERAL _0)) (real_mul x y)) (∨ (= x (real_of_num (NUMERAL _0))) (∨ (= y (real_of_num (NUMERAL _0))) (∨ (∧ (real_lt (real_of_num (NUMERAL _0)) x) (real_lt (real_of_num (NUMERAL _0)) y)) (∧ (real_lt x (real_of_num (NUMERAL _0))) (real_lt y (real_of_num (NUMERAL _0))))))))))));
