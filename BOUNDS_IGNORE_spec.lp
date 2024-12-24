require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1262185 : Prf (∀ (λ P : El (fun num num), (∀ (λ Q : El (fun num num), (= (∃ (λ B : El num, (∀ (λ i : El num, (<= (P i) (+ (Q i) B)))))) (∃ (λ B : El num, (∃ (λ N : El num, (∀ (λ i : El num, (⇒ (<= N i) (<= (P i) (+ (Q i) B))))))))))))));
