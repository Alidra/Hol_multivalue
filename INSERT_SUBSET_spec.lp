require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3287457 [A] : Prf (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (= ((@SUBSET A) ((@INSERT A) x s) t) (∧ ((@IN A) x t) ((@SUBSET A) s t)))))))));
