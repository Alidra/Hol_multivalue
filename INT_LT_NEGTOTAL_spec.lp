require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2304634 : Prf (∀ (λ x : El int, (∨ (= x (int_of_num (NUMERAL _0))) (∨ (int_lt (int_of_num (NUMERAL _0)) x) (int_lt (int_of_num (NUMERAL _0)) (int_neg x))))));
