require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2405813 (m : El num) : Prf (∧ (= (int_add (int_neg (int_of_num m)) (int_of_num m)) (int_of_num (NUMERAL _0))) (= (int_add (int_of_num m) (int_neg (int_of_num m))) (int_of_num (NUMERAL _0))));
