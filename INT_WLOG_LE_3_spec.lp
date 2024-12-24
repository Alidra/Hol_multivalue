require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2315139 : Prf (∀ (λ P : El (fun int (fun int (fun int bool))), (⇒ (∧ (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (⇒ (P x y z) (∧ (P y x z) (P x z y))))))))) (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (⇒ (∧ (int_le x y) (int_le y z)) (P x y z))))))))) (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (P x y z))))))))));
