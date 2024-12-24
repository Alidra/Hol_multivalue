require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2267745 (a : El int) : Prf (= ((λ a' : El int, (= (int_of_real (real_of_int a')) a')) a) (= (int_of_real (real_of_int a)) a));
