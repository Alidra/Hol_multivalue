require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem515614 : Prf (∧ (∀ (λ n : El num, (= (* _0 n) _0))) (∧ (∀ (λ m : El num, (= (* m _0) _0))) (∧ (∀ (λ n : El num, (= (* (BIT1 _0) n) n))) (∧ (∀ (λ m : El num, (= (* m (BIT1 _0)) m))) (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (* (SUC m) n) (+ (* m n) n)))))) (∀ (λ m : El num, (∀ (λ n : El num, (= (* m (SUC n)) (+ m (* m n))))))))))));
