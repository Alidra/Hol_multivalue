require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7160834 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ g : El (fun A real), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (⇒ (∧ ((@FINITE A) s) ((@SUBSET B) ((@IMAGE A B) f s) t)) (= ((@sum B) t (λ y : El B, ((@sum A) ((@GSPEC A) (λ GEN_PVAR_325 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_325 (∧ ((@IN A) x s) (= (f x) y)) x))))) g))) ((@sum A) s g)))))))))));
