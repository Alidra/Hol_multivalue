require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2406442 (x : El num) : Prf (∧ (= (int_abs (int_neg (int_of_num x))) (int_of_num x)) (= (int_abs (int_of_num x)) (int_of_num x)));
