require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1978412 (x1 : El real) (x2 : El real) (y1 : El real) (y2 : El real) : Prf (⇒ (∧ (real_lt (real_of_num (NUMERAL _0)) y1) (real_lt (real_of_num (NUMERAL _0)) y2)) (= (real_sub (real_div x1 y1) (real_div x2 y2)) (real_mul (real_sub (real_mul x1 y2) (real_mul x2 y1)) (real_mul (real_inv y1) (real_inv y2)))));
