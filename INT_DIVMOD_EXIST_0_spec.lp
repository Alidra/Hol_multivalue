require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2385714 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (∃ (λ q : El int, (∃ (λ r : El int, ((@COND bool) (= n (int_of_num (NUMERAL _0))) (∧ (= q (int_of_num (NUMERAL _0))) (= r m)) (∧ (int_le (int_of_num (NUMERAL _0)) r) (∧ (int_lt r (int_abs n)) (= m (int_add (int_mul q n) r)))))))))))));
