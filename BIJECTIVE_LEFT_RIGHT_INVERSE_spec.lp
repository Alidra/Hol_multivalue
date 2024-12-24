require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3576800 [A B] : Prf (∀ (λ f : El (fun A B), (= (∧ (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (= (f x) (f y)) (= x y)))))) (∀ (λ y : El B, (∃ (λ x : El A, (= (f x) y)))))) (∃ (λ g : El (fun B A), (∧ (∀ (λ y : El B, (= (f (g y)) y))) (∀ (λ x : El A, (= (g (f x)) x)))))))));
