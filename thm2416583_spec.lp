require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2416583 (y : El int) (x : El int) (z : El int) : Prf (= (int_mul x (int_add y z)) (int_add (int_mul x y) (int_mul x z)));
