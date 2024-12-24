require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2406288 (x : El int) (y : El int) : Prf (= ((λ y' : El int, (= (int_sub x y') (int_add x (int_neg y')))) y) (= (int_sub x y) (int_add x (int_neg y))));
