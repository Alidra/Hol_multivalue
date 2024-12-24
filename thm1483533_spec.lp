require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1483533 (x : El real) (y : El real) : Prf (= (¬ (real_le x y)) (real_gt (real_sub x y) (real_of_num (NUMERAL _0))));
