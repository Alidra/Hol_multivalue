require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1367246 (m : El num) (n : El num) : Prf (∧ (∧ (= (real_mul (real_of_num m) (real_of_num n)) (real_of_num (* m n))) (= (real_mul (real_neg (real_of_num m)) (real_neg (real_of_num n))) (real_of_num (* m n)))) (∧ (= (real_mul (real_neg (real_of_num m)) (real_of_num n)) (real_neg (real_of_num (* m n)))) (= (real_mul (real_of_num m) (real_neg (real_of_num n))) (real_neg (real_of_num (* m n))))));
