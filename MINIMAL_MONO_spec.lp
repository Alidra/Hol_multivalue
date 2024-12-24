require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem283487 : Prf (∀ (λ P : El (fun num bool), (∀ (λ Q : El (fun num bool), (⇒ (∧ (∃ (λ n : El num, (P n))) (∀ (λ n : El num, (⇒ (P n) (Q n))))) (<= (minimal Q) (minimal P)))))));
