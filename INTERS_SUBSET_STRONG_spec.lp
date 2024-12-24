require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3361592 [A] : Prf (∀ (λ u : El (fun (fun A bool) bool), (∀ (λ s : El (fun A bool), (⇒ (∃ (λ t : El (fun A bool), (∧ ((@IN (fun A bool)) t u) ((@SUBSET A) t s)))) ((@SUBSET A) ((@INTERS A) u) s))))));
