require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem538852 : Prf (∧ (∀ (λ n : El num, (= (+ (BIT0 n) _0) (BIT0 n)))) (∧ (∀ (λ n : El num, (= (+ (BIT1 n) _0) (BIT1 n)))) (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (+ (BIT0 m) (BIT0 n)) (BIT0 (+ m n))))))) (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (+ (BIT0 m) (BIT1 n)) (BIT1 (+ m n))))))) (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (+ (BIT1 m) (BIT0 n)) (BIT1 (+ m n))))))) (∀ (λ m : El num, (∀ (λ n : El num, (= (+ (BIT1 m) (BIT1 n)) (BIT0 (SUC (+ m n)))))))))))));
