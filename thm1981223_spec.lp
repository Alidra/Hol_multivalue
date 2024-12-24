require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1981223 (n : El num) (m : El num) : Prf (∧ (= (real_inv (real_of_num n)) (real_div (real_of_num (NUMERAL (BIT1 _0))) (real_of_num n))) (∧ (= (real_inv (real_neg (real_of_num n))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 _0)))) (real_of_num n))) (∧ (= (real_inv (real_div (real_of_num m) (real_of_num n))) (real_div (real_of_num n) (real_of_num m))) (∧ (= (real_inv (real_div (real_neg (real_of_num m)) (real_of_num n))) (real_div (real_neg (real_of_num n)) (real_of_num m))) (∧ (= (real_inv (DECIMAL m n)) (real_div (real_of_num n) (real_of_num m))) (= (real_inv (real_neg (DECIMAL m n))) (real_div (real_neg (real_of_num n)) (real_of_num m))))))));
