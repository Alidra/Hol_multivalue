require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4605019 [A] : Prf (∀ (λ P : El (fun (fun A bool) bool), (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) ((@FINITE (fun A bool)) ((@GSPEC (fun A bool)) (λ GEN_PVAR_158 : El (fun A bool), (∃ (λ t : El (fun A bool), ((@SETSPEC (fun A bool)) GEN_PVAR_158 (∧ ((@SUBSET A) t s) (P t)) t)))))))))));
