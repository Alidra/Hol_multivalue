require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2661209 : Prf (∧ (∀ (λ m : El int, (∀ (λ n : El int, (∀ (λ p : El int, (= (rem (int_add (int_mul m n) p) n) (rem p n)))))))) (∧ (∀ (λ m : El int, (∀ (λ n : El int, (∀ (λ p : El int, (= (rem (int_add (int_mul n m) p) n) (rem p n)))))))) (∧ (∀ (λ m : El int, (∀ (λ n : El int, (∀ (λ p : El int, (= (rem (int_add p (int_mul m n)) n) (rem p n)))))))) (∀ (λ m : El int, (∀ (λ n : El int, (∀ (λ p : El int, (= (rem (int_add p (int_mul n m)) n) (rem p n)))))))))));
