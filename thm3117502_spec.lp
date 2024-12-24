require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3117502 (x : El num) (y : El num) (n : El num) : Prf (= ((λ n' : El num, (= ((@== num) x y (num_mod n')) ((@== int) (int_of_num x) (int_of_num y) (int_mod (int_of_num n'))))) n) (= ((@== num) x y (num_mod n)) ((@== int) (int_of_num x) (int_of_num y) (int_mod (int_of_num n)))));
