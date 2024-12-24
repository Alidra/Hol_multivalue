require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem15397 [A B C] : Prf (∀ (λ f : El (fun B C), (∀ (λ g : El (fun A B), (= ((@o A B C) f g) (λ x : El A, (f (g x))))))));
