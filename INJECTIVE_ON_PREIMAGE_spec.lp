require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5047839 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ u : El (fun B bool), (= (∀ (λ t : El (fun B bool), (∀ (λ t' : El (fun B bool), (⇒ (∧ ((@SUBSET B) t u) (∧ ((@SUBSET B) t' u) (= ((@GSPEC A) (λ GEN_PVAR_220 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_220 (∧ ((@IN A) x s) ((@IN B) (f x) t)) x))))) ((@GSPEC A) (λ GEN_PVAR_221 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_221 (∧ ((@IN A) x s) ((@IN B) (f x) t')) x)))))))) (= t t')))))) ((@SUBSET B) u ((@IMAGE A B) f s)))))))));
