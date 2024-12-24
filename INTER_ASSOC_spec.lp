require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3255255 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (∀ (λ u : El (fun A bool), (= ((@INTER A) ((@INTER A) s t) u) ((@INTER A) s ((@INTER A) t u)))))))));
