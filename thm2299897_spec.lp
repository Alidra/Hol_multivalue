require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2299897 (x : El int) (y : El int) : Prf ((λ y' : El int, (= (real_sub (real_of_int x) (real_of_int y')) (real_of_int (int_sub x y')))) y);
