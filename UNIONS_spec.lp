require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3189257 [A] : Prf (∀ (λ s : El (fun (fun A bool) bool), (= ((@UNIONS A) s) ((@GSPEC A) (λ GEN_PVAR_1 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_1 (∃ (λ u : El (fun A bool), (∧ ((@IN (fun A bool)) u s) ((@IN A) x u)))) x))))))));
