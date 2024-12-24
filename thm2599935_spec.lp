require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2599935 : Prf (∧ (∧ (∀ (λ m : El int, (∀ (λ n : El int, (⇒ (¬ (= n (int_of_num (NUMERAL _0)))) (= (div (int_mul m n) n) m)))))) (∀ (λ m : El int, (∀ (λ n : El int, (⇒ (¬ (= m (int_of_num (NUMERAL _0)))) (= (div (int_mul m n) m) n))))))) (∧ (∀ (λ m : El int, (∀ (λ n : El int, (= (rem (int_mul m n) n) (int_of_num (NUMERAL _0))))))) (∀ (λ m : El int, (∀ (λ n : El int, (= (rem (int_mul m n) m) (int_of_num (NUMERAL _0)))))))));
