require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) (x1: El num) ≔ (∧ (= (real_add (real_of_num x0) (real_neg (real_of_num (+ x0 x1)))) (real_neg (real_of_num x1))) (= (real_add (real_of_num x0) (real_of_num x1)) (real_of_num (+ x0 x1))));
