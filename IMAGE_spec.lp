require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3199546 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A B), (= ((@IMAGE A B) f s) ((@GSPEC B) (λ GEN_PVAR_7 : El B, (∃ (λ y : El B, ((@SETSPEC B) GEN_PVAR_7 (∃ (λ x : El A, (∧ ((@IN A) x s) (= y (f x))))) y))))))))));
