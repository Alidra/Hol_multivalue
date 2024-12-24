require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2301026 (n : El int) (m : El int) : Prf (= (= (real_add (real_of_int m) (real_of_int n)) (real_add (real_of_int n) (real_of_int m))) (= (int_add m n) (int_add n m)));
