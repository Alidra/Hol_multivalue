require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2405757 (m : El num) (n : El num) : Prf (∧ (= (int_mul (int_neg (int_of_num m)) (int_of_num n)) (int_neg (int_of_num (* m n)))) (= (int_mul (int_of_num m) (int_neg (int_of_num n))) (int_neg (int_of_num (* m n)))));
