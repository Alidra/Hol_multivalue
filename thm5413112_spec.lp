require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5413112 (m : El num) (n : El num) : Prf (⇒ (<= m (SUC n)) (∀ (λ x : El num, (= (∧ (<= m x) (<= x (SUC n))) (∨ (= x (SUC n)) (∧ (<= m x) (<= x n)))))));
