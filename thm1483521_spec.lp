require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1483521 (y : El real) (x : El real) : Prf (= (real_lt x y) (real_gt (real_sub y x) (real_of_num (NUMERAL _0))));
