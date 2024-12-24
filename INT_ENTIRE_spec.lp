require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2301483 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (= (int_mul x y) (int_of_num (NUMERAL _0))) (∨ (= x (int_of_num (NUMERAL _0))) (= y (int_of_num (NUMERAL _0)))))))));
