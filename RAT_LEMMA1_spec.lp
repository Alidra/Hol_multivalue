require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1978101 (x1 : El real) (x2 : El real) (y1 : El real) (y2 : El real) : Prf (⇒ (∧ (¬ (= y1 (real_of_num (NUMERAL _0)))) (¬ (= y2 (real_of_num (NUMERAL _0))))) (= (real_add (real_div x1 y1) (real_div x2 y2)) (real_mul (real_add (real_mul x1 y2) (real_mul x2 y1)) (real_mul (real_inv y1) (real_inv y2)))));
