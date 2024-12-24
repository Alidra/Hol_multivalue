require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2405764 (x : El num) : Prf (∧ (= (int_mul (int_of_num x) (int_of_num (NUMERAL _0))) (int_of_num (NUMERAL _0))) (= (int_mul (int_neg (int_of_num x)) (int_of_num (NUMERAL _0))) (int_of_num (NUMERAL _0))));
