require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1367839 (x : El num) (n : El num) : Prf (∧ (= (real_pow (real_of_num x) n) (real_of_num (EXP x n))) (= (real_pow (real_neg (real_of_num x)) n) ((@COND real) (EVEN n) (real_of_num (EXP x n)) (real_neg (real_of_num (EXP x n))))));
