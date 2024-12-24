require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3234183 [A] : Prf (∧ (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), ((@SUBSET A) s ((@UNION A) s t)))))) (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), ((@SUBSET A) s ((@UNION A) t s)))))));
