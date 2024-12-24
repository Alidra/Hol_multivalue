require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem207311 : Prf (∧ (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (= (MOD (+ (* m n) p) n) (MOD p n)))))))) (∧ (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (= (MOD (+ (* n m) p) n) (MOD p n)))))))) (∧ (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (= (MOD (+ p (* m n)) n) (MOD p n)))))))) (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (= (MOD (+ p (* n m)) n) (MOD p n)))))))))));
