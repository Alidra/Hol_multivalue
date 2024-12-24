require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2313447 (P : El (fun int (fun int bool))) : Prf (⇒ (∧ (∀ (λ x : El int, (P x x))) (∧ (∀ (λ x : El int, (∀ (λ y : El int, (= (P x y) (P y x)))))) (∀ (λ x : El int, (∀ (λ y : El int, (⇒ (int_lt x y) (P x y)))))))) (∀ (λ x : El int, (∀ (λ y : El int, (P x y))))));
