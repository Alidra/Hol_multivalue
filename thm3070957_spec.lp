require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3070957 (m : El num) (n : El num) : Prf (= (¬ (¬ (= (= (int_of_num m) (int_of_num n)) (= (int_abs (int_of_num m)) (int_abs (int_of_num n)))))) (= (= (int_of_num m) (int_of_num n)) (= (int_abs (int_of_num m)) (int_abs (int_of_num n)))));
