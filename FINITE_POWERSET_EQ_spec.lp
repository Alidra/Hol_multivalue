require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4604266 [A] : Prf (∀ (λ s : El (fun A bool), (= ((@FINITE (fun A bool)) ((@GSPEC (fun A bool)) (λ GEN_PVAR_156 : El (fun A bool), (∃ (λ t : El (fun A bool), ((@SETSPEC (fun A bool)) GEN_PVAR_156 ((@SUBSET A) t s) t)))))) ((@FINITE A) s))));
