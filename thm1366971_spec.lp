require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1366971 (m : El num) (n : El num) : Prf (∧ (= (= (real_of_num m) (real_of_num n)) (= m n)) (∧ (= (= (real_neg (real_of_num m)) (real_neg (real_of_num n))) (= m n)) (∧ (= (= (real_neg (real_of_num m)) (real_of_num n)) (∧ (= m (NUMERAL _0)) (= n (NUMERAL _0)))) (= (= (real_of_num m) (real_neg (real_of_num n))) (∧ (= m (NUMERAL _0)) (= n (NUMERAL _0)))))));
