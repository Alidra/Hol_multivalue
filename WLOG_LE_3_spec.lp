require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem112834 : Prf (∀ (λ P : El (fun num (fun num (fun num bool))), (⇒ (∧ (∀ (λ x : El num, (∀ (λ y : El num, (∀ (λ z : El num, (⇒ (P x y z) (∧ (P y x z) (P x z y))))))))) (∀ (λ x : El num, (∀ (λ y : El num, (∀ (λ z : El num, (⇒ (∧ (<= x y) (<= y z)) (P x y z))))))))) (∀ (λ x : El num, (∀ (λ y : El num, (∀ (λ z : El num, (P x y z))))))))));
