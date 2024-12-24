require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1367768 (m : El num) (n : El num) : Prf (∧ (= (real_add (real_of_num m) (real_neg (real_of_num (+ m n)))) (real_neg (real_of_num n))) (= (real_add (real_of_num m) (real_of_num n)) (real_of_num (+ m n))));
