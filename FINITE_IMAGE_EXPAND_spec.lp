require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3615039 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) ((@FINITE B) ((@GSPEC B) (λ GEN_PVAR_94 : El B, (∃ (λ y : El B, ((@SETSPEC B) GEN_PVAR_94 (∃ (λ x : El A, (∧ ((@IN A) x s) (= y (f x))))) y)))))))))));
