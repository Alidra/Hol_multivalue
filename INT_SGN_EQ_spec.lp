require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2309449 : Prf (∧ (∀ (λ x : El int, (= (= (int_sgn x) (int_of_num (NUMERAL _0))) (= x (int_of_num (NUMERAL _0)))))) (∧ (∀ (λ x : El int, (= (= (int_sgn x) (int_of_num (NUMERAL (BIT1 _0)))) (int_gt x (int_of_num (NUMERAL _0)))))) (∀ (λ x : El int, (= (= (int_sgn x) (int_neg (int_of_num (NUMERAL (BIT1 _0))))) (int_lt x (int_of_num (NUMERAL _0))))))));
