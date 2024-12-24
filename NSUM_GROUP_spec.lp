require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6994742 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ g : El (fun A num), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (⇒ (∧ ((@FINITE A) s) ((@SUBSET B) ((@IMAGE A B) f s) t)) (= ((@nsum B) t (λ y : El B, ((@nsum A) ((@GSPEC A) (λ GEN_PVAR_296 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_296 (∧ ((@IN A) x s) (= (f x) y)) x))))) g))) ((@nsum A) s g)))))))))));
