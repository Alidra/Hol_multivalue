require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3288664 [A] : Prf (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (⇒ (¬ ((@IN A) x s)) (∀ (λ t : El (fun A bool), (= ((@SUBSET A) s ((@INSERT A) x t)) ((@SUBSET A) s t)))))))));
