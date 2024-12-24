require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3266941 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (∀ (λ u : El (fun A bool), (= ((@DISJOINT A) ((@UNION A) s t) u) (∧ ((@DISJOINT A) s u) ((@DISJOINT A) t u)))))))));
