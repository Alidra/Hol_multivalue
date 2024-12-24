require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2318532 (x : El int) (y : El int) : Prf ((λ y' : El int, (= (real_of_int (int_mul x y')) (real_mul (real_of_int x) (real_of_int y')))) y);
