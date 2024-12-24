require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2338253 (P : El (fun num bool)) : Prf (= ((λ P' : El (fun num bool), (= (∃ (λ n : El num, (P' n))) (∃ (λ n : El num, (∧ (P' n) (∀ (λ m : El num, (⇒ (< m n) (¬ (P' m)))))))))) P) (= (∃ (λ n : El num, (P n))) (∃ (λ n : El num, (∧ (P n) (∀ (λ m : El num, (⇒ (< m n) (¬ (P m))))))))));
