require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1614637 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (= (real_lt (real_of_num (NUMERAL _0)) (real_mul x y)) (∨ (∧ (real_lt (real_of_num (NUMERAL _0)) x) (real_lt (real_of_num (NUMERAL _0)) y)) (∧ (real_lt x (real_of_num (NUMERAL _0))) (real_lt y (real_of_num (NUMERAL _0))))))))));
