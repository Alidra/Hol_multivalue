require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7159247 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ g : El (fun A real), (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) (= ((@sum A) s g) ((@sum B) ((@IMAGE A B) f s) (λ y : El B, ((@sum A) ((@GSPEC A) (λ GEN_PVAR_324 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_324 (∧ ((@IN A) x s) (= (f x) y)) x))))) g)))))))))));
