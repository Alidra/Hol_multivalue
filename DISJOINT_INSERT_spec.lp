require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3286086 [A] : Prf (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (= ((@DISJOINT A) ((@INSERT A) x s) t) (∧ ((@DISJOINT A) s t) (¬ ((@IN A) x t))))))))));
