require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2299931 (x : El int) (y : El int) : Prf (= ((λ y' : El int, (= (real_ge (real_of_int x) (real_of_int y')) (int_ge x y'))) y) (= (real_ge (real_of_int x) (real_of_int y)) (int_ge x y)));
