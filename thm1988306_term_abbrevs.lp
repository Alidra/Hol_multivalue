require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El real) (x1: El real) ≔ (∧ (= (real_ge x0 x1) (real_ge (real_sub x0 x1) (real_of_num (NUMERAL _0)))) (∧ (= (= x0 x1) (= (real_sub x0 x1) (real_of_num (NUMERAL _0)))) (∧ (= (¬ (real_lt x0 x1)) (real_ge (real_sub x0 x1) (real_of_num (NUMERAL _0)))) (∧ (= (¬ (real_le x0 x1)) (real_gt (real_sub x0 x1) (real_of_num (NUMERAL _0)))) (∧ (= (¬ (real_gt x0 x1)) (real_ge (real_sub x1 x0) (real_of_num (NUMERAL _0)))) (∧ (= (¬ (real_ge x0 x1)) (real_gt (real_sub x1 x0) (real_of_num (NUMERAL _0)))) (= (¬ (= x0 x1)) (∨ (real_gt (real_sub x0 x1) (real_of_num (NUMERAL _0))) (real_gt (real_neg (real_sub x0 x1)) (real_of_num (NUMERAL _0)))))))))));
