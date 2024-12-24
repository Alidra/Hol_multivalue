require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4614687 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@INFINITE A) s) ((@FINITE B) ((@IMAGE A B) f s))) (∃ (λ a : El A, (∧ ((@IN A) a s) ((@INFINITE A) ((@GSPEC A) (λ GEN_PVAR_169 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_169 (∧ ((@IN A) x s) (= (f x) (f a))) x))))))))))))));
