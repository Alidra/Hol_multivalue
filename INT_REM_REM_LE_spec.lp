require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2651482 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (∀ (λ p : El int, (⇒ (∧ (¬ (= n (int_of_num (NUMERAL _0)))) (int_le (int_abs n) (int_abs p))) (= (rem (rem m n) p) (rem m n)))))))));
