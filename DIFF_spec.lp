require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3192076 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (= ((@DIFF A) s t) ((@GSPEC A) (λ GEN_PVAR_4 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_4 (∧ ((@IN A) x s) (¬ ((@IN A) x t))) x))))))))));
