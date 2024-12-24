require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1267473 : Prf (∀ (λ x : El nadd, (∀ (λ y : El nadd, (∃ (λ A : El num, (∃ (λ B : El num, (∀ (λ n : El num, (<= (dist ((@̦‚ num num) (* n (dest_nadd x (dest_nadd y n))) (* (dest_nadd x n) (dest_nadd y n)))) (+ (* A n) B))))))))))));
