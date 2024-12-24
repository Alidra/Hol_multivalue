require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3603906 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ P : El (fun A bool), (⇒ ((@FINITE A) s) ((@FINITE A) ((@GSPEC A) (λ GEN_PVAR_91 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_91 (∧ ((@IN A) x s) (P x)) x)))))))))));
