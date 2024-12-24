require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3400493 [A] : Prf (∀ (λ s : El (fun A bool), (= ((@GSPEC A) (λ GEN_PVAR_30 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_30 ((@IN A) x s) x))))) s)));
