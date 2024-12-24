require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1980010 (x : El num) (y : El num) : Prf (∧ (= (real_of_num x) (real_div (real_of_num x) (real_of_num (NUMERAL (BIT1 _0))))) (∧ (= (real_neg (real_of_num x)) (real_div (real_neg (real_of_num x)) (real_of_num (NUMERAL (BIT1 _0))))) (∧ (= (DECIMAL x y) (real_div (real_of_num x) (real_of_num y))) (= (real_neg (DECIMAL x y)) (real_div (real_neg (real_of_num x)) (real_of_num y))))));
