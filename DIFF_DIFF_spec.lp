require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3270115 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (= ((@DIFF A) ((@DIFF A) s t) t) ((@DIFF A) s t))))));
