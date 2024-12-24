require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem117739 : Prf (∀ (λ P : El (fun num bool), (= (∧ (∃ (λ x : El num, (P x))) (∃ (λ M : El num, (∀ (λ x : El num, (⇒ (P x) (<= x M))))))) (∃ (λ m : El num, (∧ (P m) (∀ (λ x : El num, (⇒ (P x) (<= x m))))))))));
