require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7188904 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ P : El (fun A bool), (∀ (λ f : El (fun A real), (∀ (λ g : El (fun A real), (⇒ ((@FINITE A) s) (= ((@sum A) s (λ x : El A, ((@COND real) (P x) (f x) (g x)))) (real_add ((@sum A) ((@GSPEC A) (λ GEN_PVAR_328 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_328 (∧ ((@IN A) x s) (P x)) x))))) f) ((@sum A) ((@GSPEC A) (λ GEN_PVAR_329 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_329 (∧ ((@IN A) x s) (¬ (P x))) x))))) g))))))))))));
