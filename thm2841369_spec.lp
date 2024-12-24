require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2841369 (m : El num) (n : El num) : Prf (= ((λ n' : El num, (= (int_of_num (MIN m n')) (int_min (int_of_num m) (int_of_num n')))) n) (= (int_of_num (MIN m n)) (int_min (int_of_num m) (int_of_num n))));
