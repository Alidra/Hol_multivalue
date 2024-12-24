require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem519779 : Prf (∧ (<= _0 _0) (∧ (∀ (λ n : El num, (= (<= (+ n n) _0) (<= n _0)))) (∧ (∀ (λ n : El num, (¬ (<= (SUC (+ n n)) _0)))) (∧ (∀ (λ n : El num, (<= _0 (+ n n)))) (∧ (∀ (λ n : El num, (<= _0 (SUC (+ n n))))) (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (<= (+ m m) (+ n n)) (<= m n)))))) (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (<= (+ m m) (SUC (+ n n))) (<= m n)))))) (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (<= (SUC (+ m m)) (+ n n)) (< m n)))))) (∀ (λ m : El num, (∀ (λ n : El num, (= (<= (SUC (+ m m)) (SUC (+ n n))) (<= m n))))))))))))));
