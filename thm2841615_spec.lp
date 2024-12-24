require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2841615 (x : El int) (y : El int) : Prf ((λ y' : El int, (= (int_le x y') (real_le (real_of_int x) (real_of_int y')))) y);
