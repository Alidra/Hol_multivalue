require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5401059 (m : El num) (n : El num) : Prf (= (∀ (λ x : El num, (= (∧ (<= m x) (<= x (SUC n))) (∧ (<= m x) (<= x n))))) (∀ (λ x : El num, (= ((@IN num) x (… m (SUC n))) ((@IN num) x (… m n))))));
