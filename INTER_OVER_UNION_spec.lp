require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3263548 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (∀ (λ u : El (fun A bool), (= ((@UNION A) s ((@INTER A) t u)) ((@INTER A) ((@UNION A) s t) ((@UNION A) s u)))))))));
