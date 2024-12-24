require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1367303 (m : El num) : Prf (∧ (= (real_add (real_neg (real_of_num m)) (real_of_num m)) (real_of_num (NUMERAL _0))) (= (real_add (real_of_num m) (real_neg (real_of_num m))) (real_of_num (NUMERAL _0))));
