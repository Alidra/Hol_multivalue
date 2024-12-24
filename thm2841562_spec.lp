require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2841562 (x : El int) : Prf (= ((λ x' : El int, (= (real_of_int (int_abs x')) (real_abs (real_of_int x')))) x) (= (real_of_int (int_abs x)) (real_abs (real_of_int x))));
