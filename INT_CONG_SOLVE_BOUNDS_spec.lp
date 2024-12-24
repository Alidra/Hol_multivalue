require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2531813 : Prf (∀ (λ a : El int, (∀ (λ n : El int, (⇒ (¬ (= n (int_of_num (NUMERAL _0)))) (∃ (λ x : El int, (∧ (int_le (int_of_num (NUMERAL _0)) x) (∧ (int_lt x (int_abs n)) ((@== int) x a (int_mod n)))))))))));
