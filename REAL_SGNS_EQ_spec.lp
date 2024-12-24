require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1843951 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (= (= (real_sgn x) (real_sgn y)) (∧ (= (= x (real_of_num (NUMERAL _0))) (= y (real_of_num (NUMERAL _0)))) (∧ (= (real_gt x (real_of_num (NUMERAL _0))) (real_gt y (real_of_num (NUMERAL _0)))) (= (real_lt x (real_of_num (NUMERAL _0))) (real_lt y (real_of_num (NUMERAL _0)))))))))));
