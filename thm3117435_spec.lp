require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3117435 (m : El num) (n : El num) : Prf ((λ n' : El num, (= (int_of_num (* m n')) (int_mul (int_of_num m) (int_of_num n')))) n);
