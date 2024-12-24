require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2405481 (m : El num) (n : El num) : Prf (∧ (= (= (int_of_num m) (int_of_num n)) (= m n)) (∧ (= (= (int_neg (int_of_num m)) (int_neg (int_of_num n))) (= m n)) (∧ (= (= (int_neg (int_of_num m)) (int_of_num n)) (∧ (= m (NUMERAL _0)) (= n (NUMERAL _0)))) (= (= (int_of_num m) (int_neg (int_of_num n))) (∧ (= m (NUMERAL _0)) (= n (NUMERAL _0)))))));
