require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2304933 : Prf (∀ (λ x : El int, (= (int_lt (int_of_num (NUMERAL _0)) (int_mul x x)) (¬ (= x (int_of_num (NUMERAL _0)))))));
