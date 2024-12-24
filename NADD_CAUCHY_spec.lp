require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1262851 : Prf (∀ (λ x : El nadd, (∃ (λ B : El num, (∀ (λ m : El num, (∀ (λ n : El num, (<= (dist ((@̦‚ num num) (* m (dest_nadd x n)) (* n (dest_nadd x m)))) (* B (+ m n)))))))))));
