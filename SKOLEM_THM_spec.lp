require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem13546 [A B] : Prf (∀ (λ P : El (fun A (fun B bool)), (= (∀ (λ x : El A, (∃ (λ y : El B, (P x y))))) (∃ (λ y : El (fun A B), (∀ (λ x : El A, (P x (y x)))))))));
