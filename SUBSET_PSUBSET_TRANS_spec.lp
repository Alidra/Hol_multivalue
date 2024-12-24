require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3227973 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (∀ (λ u : El (fun A bool), (⇒ (∧ ((@SUBSET A) s t) ((@PSUBSET A) t u)) ((@PSUBSET A) s u))))))));
