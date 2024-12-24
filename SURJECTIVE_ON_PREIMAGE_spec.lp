require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5055298 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ u : El (fun B bool), (= (∀ (λ k : El (fun A bool), (⇒ ((@SUBSET A) k s) (∃ (λ t : El (fun B bool), (∧ ((@SUBSET B) t u) (= ((@GSPEC A) (λ GEN_PVAR_222 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_222 (∧ ((@IN A) x s) ((@IN B) (f x) t)) x))))) k))))))) (∧ ((@SUBSET B) ((@IMAGE A B) f s) u) (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x s) (∧ ((@IN A) y s) (= (f x) (f y)))) (= x y))))))))))))));
