require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1075149 [A B] : Prf (∀ (λ g : El (fun B A), (∀ (λ f : El (fun A B), (= ((@ISO A B) f g) (∧ (∀ (λ x : El B, (= (f (g x)) x))) (∀ (λ y : El A, (= (g (f y)) y)))))))));
