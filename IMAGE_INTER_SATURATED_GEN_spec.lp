require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3493630 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (∀ (λ u : El (fun A bool), (⇒ (∨ (∧ ((@SUBSET A) ((@GSPEC A) (λ GEN_PVAR_82 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_82 (∧ ((@IN A) x u) ((@IN B) (f x) ((@IMAGE A B) f s))) x))))) s) ((@SUBSET A) t u)) (∧ ((@SUBSET A) ((@GSPEC A) (λ GEN_PVAR_83 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_83 (∧ ((@IN A) x u) ((@IN B) (f x) ((@IMAGE A B) f t))) x))))) t) ((@SUBSET A) s u))) (= ((@IMAGE A B) f ((@INTER A) s t)) ((@INTER B) ((@IMAGE A B) f s) ((@IMAGE A B) f t))))))))))));
