require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4323219 [A B C] : Prf (∀ (λ f : El (fun A (fun B C)), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A (fun B bool)), (⇒ (∧ ((@FINITE A) s) (∀ (λ x : El A, (⇒ ((@IN A) x s) ((@FINITE B) (t x)))))) ((@FINITE C) ((@GSPEC C) (λ GEN_PVAR_126 : El C, (∃ (λ x : El A, (∃ (λ y : El B, ((@SETSPEC C) GEN_PVAR_126 (∧ ((@IN A) x s) ((@IN B) y (t x))) (f x y))))))))))))))));
