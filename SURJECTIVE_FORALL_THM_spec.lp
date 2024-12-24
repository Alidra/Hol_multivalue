require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3585065 [A B] : Prf (∀ (λ f : El (fun A B), (= (∀ (λ y : El B, (∃ (λ x : El A, (= (f x) y))))) (∀ (λ P : El (fun B bool), (= (∀ (λ x : El A, (P (f x)))) (∀ (λ y : El B, (P y)))))))));
