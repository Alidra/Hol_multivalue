require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2299924 (x : El int) (y : El int) : Prf ((λ y' : El int, (= (real_gt (real_of_int x) (real_of_int y')) (int_gt x y'))) y);
