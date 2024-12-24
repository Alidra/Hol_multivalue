require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3556761 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun A bool), (⇒ (∨ ((@SUBSET A) ((@GSPEC A) (λ GEN_PVAR_86 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_86 ((@IN B) (f x) ((@IMAGE A B) f s)) x))))) s) ((@SUBSET A) ((@GSPEC A) (λ GEN_PVAR_87 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_87 ((@IN B) (f x) ((@IMAGE A B) f t)) x))))) t)) (= ((@IMAGE A B) f ((@INTER A) s t)) ((@INTER B) ((@IMAGE A B) f s) ((@IMAGE A B) f t))))))))));
