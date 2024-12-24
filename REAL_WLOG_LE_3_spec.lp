require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1868204 : Prf (∀ (λ P : El (fun real (fun real (fun real bool))), (⇒ (∧ (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (⇒ (P x y z) (∧ (P y x z) (P x z y))))))))) (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (⇒ (∧ (real_le x y) (real_le y z)) (P x y z))))))))) (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (P x y z))))))))));
