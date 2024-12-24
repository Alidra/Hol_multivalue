require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2267740 (r : El real) : Prf ((λ r' : El real, (= (integer r') (= (real_of_int (int_of_real r')) r'))) r);
