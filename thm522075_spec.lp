require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem522075 : Prf (∧ (∀ (λ n : El num, (= (<= n _0) (∧ (<= n _0) (<= _0 n))))) (∧ (∀ (λ n : El num, (= (<= n _0) (∧ (<= _0 n) (<= n _0))))) (∧ (∀ (λ m : El num, (∀ (λ n : El num, (¬ (∧ (<= m n) (< n m))))))) (∀ (λ m : El num, (∀ (λ n : El num, (¬ (∧ (< m n) (<= n m))))))))));
