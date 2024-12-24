require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2495588 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (∀ (λ q : El int, (∀ (λ r : El int, (⇒ (∧ (= m (int_add (int_mul q n) r)) (∧ (int_le (int_of_num (NUMERAL _0)) r) (int_lt r (int_abs n)))) (∧ (= (div m n) q) (= (rem m n) r)))))))))));
