require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1864819 (P : El (fun real (fun real bool))) : Prf (⇒ (∧ (∀ (λ x : El real, (∀ (λ y : El real, (= (P x y) (P y x)))))) (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (real_le x y) (P x y))))))) (∀ (λ x : El real, (∀ (λ y : El real, (P x y))))));
