require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2299901 (x : El int) : Prf (= ((λ x' : El int, (= (real_sgn (real_of_int x')) (real_of_int (int_sgn x')))) x) (= (real_sgn (real_of_int x)) (real_of_int (int_sgn x))));
