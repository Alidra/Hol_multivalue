require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5418283 (m : El num) (n : El num) (h1 : Prf (¬ (<= m (SUC n)))) : Prf (∀ (λ x : El num, (= (∧ (<= m x) (<= x (SUC n))) (∧ (<= m x) (<= x n)))));
