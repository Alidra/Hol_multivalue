require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem421 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ y : El A, (= ((λ x : El A, (f x)) y) (f y))))));
