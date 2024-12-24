require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2750525 [A B] : Prf (∀ (λ P : El (fun A (fun B bool)), (∀ (λ m : El (fun A (fun B int)), (⇒ (∧ (∀ (λ x : El A, (∀ (λ y : El B, (int_le (int_of_num (NUMERAL _0)) (m x y)))))) (∀ (λ x : El A, (∀ (λ y : El B, (⇒ (∀ (λ x' : El A, (∀ (λ y' : El B, (⇒ (int_lt (m x' y') (m x y)) (P x' y')))))) (P x y))))))) (∀ (λ x : El A, (∀ (λ y : El B, (P x y))))))))));
