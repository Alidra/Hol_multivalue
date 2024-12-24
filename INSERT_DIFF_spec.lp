require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3291085 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (∀ (λ x : El A, (= ((@DIFF A) ((@INSERT A) x s) t) ((@COND (fun A bool)) ((@IN A) x t) ((@DIFF A) s t) ((@INSERT A) x ((@DIFF A) s t))))))))));
