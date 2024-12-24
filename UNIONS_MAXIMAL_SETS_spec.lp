require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3754706 [A] : Prf (∀ (λ f : El (fun (fun A bool) bool), (⇒ ((@FINITE (fun A bool)) f) (= ((@UNIONS A) ((@GSPEC (fun A bool)) (λ GEN_PVAR_104 : El (fun A bool), (∃ (λ t : El (fun A bool), ((@SETSPEC (fun A bool)) GEN_PVAR_104 (∧ ((@IN (fun A bool)) t f) (∀ (λ u : El (fun A bool), (⇒ ((@IN (fun A bool)) u f) (¬ ((@PSUBSET A) t u)))))) t)))))) ((@UNIONS A) f)))));
