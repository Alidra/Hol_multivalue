require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2841375 (m : El num) (n : El num) : Prf (= ((λ n' : El num, (= (int_of_num (MAX m n')) (int_max (int_of_num m) (int_of_num n')))) n) (= (int_of_num (MAX m n)) (int_max (int_of_num m) (int_of_num n))));
