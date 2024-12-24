require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3232747 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (∀ (λ u : El (fun A bool), (= ((@UNION A) ((@UNION A) s t) u) ((@UNION A) s ((@UNION A) t u)))))))));
