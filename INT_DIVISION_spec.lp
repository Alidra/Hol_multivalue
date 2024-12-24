require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2389435 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (⇒ (¬ (= n (int_of_num (NUMERAL _0)))) (∧ (= m (int_add (int_mul (div m n) n) (rem m n))) (∧ (int_le (int_of_num (NUMERAL _0)) (rem m n)) (int_lt (rem m n) (int_abs n)))))))));
