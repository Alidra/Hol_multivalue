require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3211751 [A] (s : El (fun A bool)) (t : El (fun A bool)) : Prf (= ((λ t' : El (fun A bool), (= ((@SUBSET A) s t') (∀ (λ x : El A, (⇒ ((@IN A) x s) ((@IN A) x t')))))) t) (= ((@SUBSET A) s t) (∀ (λ x : El A, (⇒ ((@IN A) x s) ((@IN A) x t))))));
