require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem9220 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ g : El (fun A B), (= (= f g) (∀ (λ x : El A, (= (f x) (g x)))))))));
