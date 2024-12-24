require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2528100 : Prf (∧ (∀ (λ m : El int, (∀ (λ n : El int, (= (= (int_mul n (div m n)) m) (int_divides n m)))))) (∀ (λ m : El int, (∀ (λ n : El int, (= (= (int_mul (div m n) n) m) (int_divides n m)))))));
