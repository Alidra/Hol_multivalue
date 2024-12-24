require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) (x1: El num) ≔ (∧ (= (real_neg (real_of_num x0)) (real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 _0))))) (∧ (= (DECIMAL x0 x1) (real_div (real_of_num x0) (real_of_num x1))) (= (real_neg (DECIMAL x0 x1)) (real_div (real_neg (real_of_num x0)) (real_of_num x1)))));
