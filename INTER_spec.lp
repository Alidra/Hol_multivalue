require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3190197 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (= ((@INTER A) s t) ((@GSPEC A) (λ GEN_PVAR_2 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_2 (∧ ((@IN A) x s) ((@IN A) x t)) x))))))))));
