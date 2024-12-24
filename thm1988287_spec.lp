require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1988287 (y : El real) (x : El real) : Prf (= (real_le x y) (real_ge (real_sub y x) (real_of_num (NUMERAL _0))));
