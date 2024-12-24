require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2502332 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (⇒ (∧ (⇒ (¬ (= n (int_of_num (NUMERAL _0)))) (int_le (int_of_num (NUMERAL _0)) m)) (int_lt m n)) (= (rem m n) m))))));
