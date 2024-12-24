require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3272928 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ x : El A, (= ((@IN A) x s) (∃ (λ t : El (fun A bool), (∧ (= s ((@INSERT A) x t)) (¬ ((@IN A) x t))))))))));
