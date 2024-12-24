require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3181245 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (= (= s t) (∀ (λ x : El A, (= ((@IN A) x s) ((@IN A) x t)))))))));
