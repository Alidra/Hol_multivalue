require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3465953 [A] : Prf (∀ (λ s : El (fun A bool), (= ((@UNIONS A) ((@GSPEC (fun A bool)) (λ GEN_PVAR_63 : El (fun A bool), (∃ (λ x : El A, ((@SETSPEC (fun A bool)) GEN_PVAR_63 ((@IN A) x s) ((@INSERT A) x (@EMPTY A)))))))) s)));
