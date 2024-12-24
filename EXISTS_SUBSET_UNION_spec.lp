require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3247663 [A] (P : El (fun (fun A bool) bool)) : Prf (∀ (λ t : El (fun A bool), (∀ (λ u : El (fun A bool), (= (∃ (λ s : El (fun A bool), (∧ ((@SUBSET A) s ((@UNION A) t u)) (P s)))) (∃ (λ t' : El (fun A bool), (∃ (λ u' : El (fun A bool), (∧ ((@SUBSET A) t' t) (∧ ((@SUBSET A) u' u) (P ((@UNION A) t' u')))))))))))));
