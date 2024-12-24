require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem528115 : Prf (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (+ (BIT0 m) (BIT1 n)) (BIT1 (+ m n))))))) (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (+ (BIT1 m) (BIT0 n)) (BIT1 (+ m n))))))) (∀ (λ m : El num, (∀ (λ n : El num, (= (+ (BIT1 m) (BIT1 n)) (BIT0 (SUC (+ m n))))))))));
