require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem513125 : Prf (∧ (∀ (λ n : El num, (= (+ _0 n) n))) (∧ (∀ (λ m : El num, (= (+ m _0) m))) (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (+ (SUC m) n) (SUC (+ m n))))))) (∀ (λ m : El num, (∀ (λ n : El num, (= (+ m (SUC n)) (SUC (+ m n))))))))));
