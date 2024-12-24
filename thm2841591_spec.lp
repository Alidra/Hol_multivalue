require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2841591 (n : El num) : Prf ((λ n' : El num, (= (real_of_int (int_of_num n')) (real_of_num n'))) n);
