require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247096 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (= (<= (dist ((@̦‚ num num) m n)) p) (∧ (<= m (+ n p)) (<= n (+ m p))))))))));
