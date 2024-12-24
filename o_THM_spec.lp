require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem15456 [A B C] : Prf (∀ (λ f : El (fun B C), (∀ (λ g : El (fun A B), (∀ (λ x : El A, (= ((@o A B C) f g x) (f (g x)))))))));
