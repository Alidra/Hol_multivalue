require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1365403 (m : El num) (n : El num) : Prf (∧ (= (real_le (real_neg (real_of_num m)) (real_of_num n)) T) (∧ (= (real_le (real_of_num m) (real_of_num n)) (<= m n)) (∧ (= (real_le (real_neg (real_of_num m)) (real_neg (real_of_num n))) (<= n m)) (= (real_le (real_of_num m) (real_neg (real_of_num n))) (∧ (= m (NUMERAL _0)) (= n (NUMERAL _0)))))));
