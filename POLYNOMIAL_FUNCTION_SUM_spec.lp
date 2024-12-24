require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7581711 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ p : El (fun real (fun A real)), (⇒ (∧ ((@FINITE A) s) (∀ (λ i : El A, (⇒ ((@IN A) i s) (polynomial_function (λ x : El real, (p x i))))))) (polynomial_function (λ x : El real, ((@sum A) s (p x)))))))));
