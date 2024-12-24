require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1483550 (x : El real) (y : El real) : Prf (∧ (= (¬ (real_gt x y)) (real_ge (real_sub y x) (real_of_num (NUMERAL _0)))) (∧ (= (¬ (real_ge x y)) (real_gt (real_sub y x) (real_of_num (NUMERAL _0)))) (= (¬ (= x y)) (∨ (real_gt (real_sub x y) (real_of_num (NUMERAL _0))) (real_gt (real_neg (real_sub x y)) (real_of_num (NUMERAL _0)))))));
