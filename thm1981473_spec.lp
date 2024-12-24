require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1981473 (x1 : El real) (y1 : El real) (x2 : El real) (y2 : El real) (x3 : El real) (y3 : El real) : Prf (⇒ (real_lt (real_of_num (NUMERAL _0)) y1) (⇒ (real_lt (real_of_num (NUMERAL _0)) y2) (⇒ (real_lt (real_of_num (NUMERAL _0)) y3) (⇒ (= (real_mul (real_add (real_mul x1 y2) (real_mul x2 y1)) y3) (real_mul x3 (real_mul y1 y2))) (= (real_add (real_div x1 y1) (real_div x2 y2)) (real_div x3 y3))))));
