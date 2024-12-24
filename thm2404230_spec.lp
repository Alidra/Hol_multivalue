require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2404230 (m : El num) (n : El num) : Prf (∧ (= (int_lt (int_of_num m) (int_neg (int_of_num n))) F) (∧ (= (int_lt (int_of_num m) (int_of_num n)) (< m n)) (∧ (= (int_lt (int_neg (int_of_num m)) (int_neg (int_of_num n))) (< n m)) (= (int_lt (int_neg (int_of_num m)) (int_of_num n)) (¬ (∧ (= m (NUMERAL _0)) (= n (NUMERAL _0))))))));
