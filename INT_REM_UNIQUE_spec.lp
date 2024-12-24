require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2649536 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (∀ (λ p : El int, (= (= (rem m n) p) (∧ (∨ (∧ (= n (int_of_num (NUMERAL _0))) (= m p)) (∧ (int_le (int_of_num (NUMERAL _0)) p) (int_lt p (int_abs n)))) ((@== int) m p (int_mod n))))))))));
