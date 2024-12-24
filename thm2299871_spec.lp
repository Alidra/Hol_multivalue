require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2299871 (b : El bool) (x : El int) (y : El int) : Prf (= (= (real_of_int ((@COND int) b x y)) ((@COND real) b (real_of_int x) (real_of_int y))) (= ((@COND real) b (real_of_int x) (real_of_int y)) (real_of_int ((@COND int) b x y))));
