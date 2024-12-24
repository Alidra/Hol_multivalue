require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2625414 : Prf (∧ (∀ (λ m : El int, (∀ (λ n : El int, (∀ (λ p : El int, (⇒ (int_le (int_of_num (NUMERAL _0)) n) (= (div (div m n) p) (div m (int_mul n p)))))))))) (∀ (λ m : El int, (∀ (λ n : El int, (∀ (λ p : El int, (⇒ (int_le (int_of_num (NUMERAL _0)) n) (= (rem m (int_mul n p)) (int_add (int_mul n (rem (div m n) p)) (rem m n)))))))))));
