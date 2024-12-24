require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3217353 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (∀ (λ u : El (fun A bool), (⇒ (∧ ((@SUBSET A) s t) ((@SUBSET A) t u)) ((@SUBSET A) s u))))))));
