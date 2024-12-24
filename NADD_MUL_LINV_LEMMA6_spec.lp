require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1304593 : Prf (∀ (λ x : El nadd, (⇒ (¬ (nadd_eq x (nadd_of_num (NUMERAL _0)))) (∃ (λ B : El num, (∃ (λ N : El num, (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∧ (<= N m) (<= N n)) (<= (* (* m n) (dist ((@̦‚ num num) (* m (nadd_rinv x n)) (* n (nadd_rinv x m))))) (* B (* (* m n) (+ m n))))))))))))))));
