require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2387577 : Prf (∀ (λ m : El int, (∀ (λ n : El int, ((@COND bool) (= n (int_of_num (NUMERAL _0))) (∧ (= (div m n) (int_of_num (NUMERAL _0))) (= (rem m n) m)) (∧ (int_le (int_of_num (NUMERAL _0)) (rem m n)) (∧ (int_lt (rem m n) (int_abs n)) (= m (int_add (int_mul (div m n) n) (rem m n))))))))));
