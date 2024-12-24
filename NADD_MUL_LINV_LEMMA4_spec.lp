require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1302948 : Prf (∀ (λ x : El nadd, (⇒ (¬ (nadd_eq x (nadd_of_num (NUMERAL _0)))) (∃ (λ N : El num, (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∧ (<= N m) (<= N n)) (<= (* (* (dest_nadd x m) (dest_nadd x n)) (dist ((@̦‚ num num) (* m (nadd_rinv x n)) (* n (nadd_rinv x m))))) (+ (* (* m n) (dist ((@̦‚ num num) (* m (dest_nadd x n)) (* n (dest_nadd x m))))) (* (* (dest_nadd x m) (dest_nadd x n)) (+ m n))))))))))))));
