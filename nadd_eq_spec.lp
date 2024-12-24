require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1267930 : Prf (∀ (λ x : El nadd, (∀ (λ y : El nadd, (= (nadd_eq x y) (∃ (λ B : El num, (∀ (λ n : El num, (<= (dist ((@̦‚ num num) (dest_nadd x n) (dest_nadd y n))) B))))))))));
