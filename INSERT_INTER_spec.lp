require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3284766 [A] : Prf (∀ (λ x : El A, (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (= ((@INTER A) ((@INSERT A) x s) t) ((@COND (fun A bool)) ((@IN A) x t) ((@INSERT A) x ((@INTER A) s t)) ((@INTER A) s t)))))))));
