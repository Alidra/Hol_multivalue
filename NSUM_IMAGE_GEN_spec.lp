require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6993167 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ g : El (fun A num), (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) (= ((@nsum A) s g) ((@nsum B) ((@IMAGE A B) f s) (λ y : El B, ((@nsum A) ((@GSPEC A) (λ GEN_PVAR_295 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_295 (∧ ((@IN A) x s) (= (f x) y)) x))))) g)))))))))));
