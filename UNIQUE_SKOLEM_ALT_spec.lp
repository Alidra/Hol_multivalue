require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem13833 [A B] : Prf (∀ (λ P : El (fun A (fun B bool)), (= (∀ (λ x : El A, ((@∃! B) (λ y : El B, (P x y))))) (∃ (λ f : El (fun A B), (∀ (λ x : El A, (∀ (λ y : El B, (= (P x y) (= (f x) y)))))))))));
