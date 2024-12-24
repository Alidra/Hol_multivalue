require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1262615 : Prf (∀ (λ x : El (fun num num), (= (is_nadd x) (∃ (λ B : El num, (∀ (λ m : El num, (∀ (λ n : El num, (<= (dist ((@̦‚ num num) (* m (x n)) (* n (x m)))) (* B (+ m n))))))))))));
