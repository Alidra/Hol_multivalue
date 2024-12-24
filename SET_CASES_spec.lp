require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3275014 [A] : Prf (∀ (λ s : El (fun A bool), (∨ (= s (@EMPTY A)) (∃ (λ x : El A, (∃ (λ t : El (fun A bool), (∧ (= s ((@INSERT A) x t)) (¬ ((@IN A) x t))))))))));
