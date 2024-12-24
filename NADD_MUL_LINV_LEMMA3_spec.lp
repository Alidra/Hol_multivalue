require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1302302 : Prf (∀ (λ x : El nadd, (⇒ (¬ (nadd_eq x (nadd_of_num (NUMERAL _0)))) (∃ (λ N : El num, (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (<= N n) (<= (dist ((@̦‚ num num) (* m (* (dest_nadd x m) (* (dest_nadd x n) (nadd_rinv x n)))) (* m (* (dest_nadd x m) (* n n))))) (* m (* (dest_nadd x m) (dest_nadd x n))))))))))))));
