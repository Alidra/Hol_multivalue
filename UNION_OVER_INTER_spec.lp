require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3262316 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (∀ (λ u : El (fun A bool), (= ((@INTER A) s ((@UNION A) t u)) ((@UNION A) ((@INTER A) s t) ((@INTER A) s u)))))))));
