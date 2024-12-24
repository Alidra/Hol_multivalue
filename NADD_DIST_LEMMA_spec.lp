require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1266957 : Prf (∀ (λ x : El nadd, (∃ (λ B : El num, (∀ (λ m : El num, (∀ (λ n : El num, (<= (dist ((@̦‚ num num) (dest_nadd x (+ m n)) (dest_nadd x m))) (* B n))))))))));
