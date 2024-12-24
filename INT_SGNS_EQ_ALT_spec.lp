require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2309229 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (= (int_sgn x) (int_sgn y)) (∧ (⇒ (= x (int_of_num (NUMERAL _0))) (= y (int_of_num (NUMERAL _0)))) (∧ (⇒ (int_gt x (int_of_num (NUMERAL _0))) (int_gt y (int_of_num (NUMERAL _0)))) (⇒ (int_lt x (int_of_num (NUMERAL _0))) (int_lt y (int_of_num (NUMERAL _0)))))))))));
