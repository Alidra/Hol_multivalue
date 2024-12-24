require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1261317 : Prf (∀ (λ P : El (fun num num), (= (∃ (λ B : El num, (∀ (λ n : El num, (<= (P n) B))))) (∃ (λ A : El num, (∃ (λ B : El num, (∀ (λ n : El num, (<= (* n (P n)) (+ (* A n) B)))))))))));
