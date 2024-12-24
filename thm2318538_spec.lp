require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2318538 (x : El int) (y : El int) : Prf ((λ y' : El int, (= (real_of_int (int_add x y')) (real_add (real_of_int x) (real_of_int y')))) y);
