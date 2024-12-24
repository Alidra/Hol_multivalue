require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2305916 (n : El int) (m : El int) : Prf (= (= (real_mul (real_of_int m) (real_of_int n)) (real_mul (real_of_int n) (real_of_int m))) (= (int_mul m n) (int_mul n m)));
