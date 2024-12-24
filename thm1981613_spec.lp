require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1981613 (x1 : El real) (x2 : El real) (y1 : El real) (y2 : El real) : Prf (= (real_mul (real_div x1 y1) (real_div x2 y2)) (real_div (real_mul x1 x2) (real_mul y1 y2)));
