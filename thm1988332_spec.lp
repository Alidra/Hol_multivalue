require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1988332 (x : El real) (y : El real) : Prf (∧ (⇒ (∧ (real_gt x (real_of_num (NUMERAL _0))) (real_ge y (real_of_num (NUMERAL _0)))) (real_ge (real_mul x y) (real_of_num (NUMERAL _0)))) (⇒ (∧ (real_gt x (real_of_num (NUMERAL _0))) (real_gt y (real_of_num (NUMERAL _0)))) (real_gt (real_mul x y) (real_of_num (NUMERAL _0)))));
