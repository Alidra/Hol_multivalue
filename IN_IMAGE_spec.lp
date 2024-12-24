require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3206070 [A B] : Prf (∀ (λ y : El B, (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A B), (= ((@IN B) y ((@IMAGE A B) f s)) (∃ (λ x : El A, (∧ (= y (f x)) ((@IN A) x s)))))))))));
