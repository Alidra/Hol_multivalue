require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2299877 (x : El int) (n : El num) : Prf (= ((λ n' : El num, (= (real_pow (real_of_int x) n') (real_of_int (int_pow x n')))) n) (= (real_pow (real_of_int x) n) (real_of_int (int_pow x n))));
