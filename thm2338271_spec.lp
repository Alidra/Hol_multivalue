require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2338271 (m : El num) (n : El num) : Prf ((λ n' : El num, (= (int_le (int_of_num m) (int_of_num n')) (<= m n'))) n);
