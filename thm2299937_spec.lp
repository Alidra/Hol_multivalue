require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2299937 (x : El int) (y : El int) : Prf (= ((λ y' : El int, (= (real_lt (real_of_int x) (real_of_int y')) (int_lt x y'))) y) (= (real_lt (real_of_int x) (real_of_int y)) (int_lt x y)));
