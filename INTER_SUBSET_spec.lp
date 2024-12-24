require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3256723 [A] : Prf (∧ (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), ((@SUBSET A) ((@INTER A) s t) s))))) (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), ((@SUBSET A) ((@INTER A) t s) s))))));
