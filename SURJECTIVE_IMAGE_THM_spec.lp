require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3588668 [A B] : Prf (∀ (λ f : El (fun A B), (= (∀ (λ y : El B, (∃ (λ x : El A, (= (f x) y))))) (∀ (λ P : El (fun B bool), (= ((@IMAGE A B) f ((@GSPEC A) (λ GEN_PVAR_89 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_89 (P (f x)) x)))))) ((@GSPEC B) (λ GEN_PVAR_90 : El B, (∃ (λ x : El B, ((@SETSPEC B) GEN_PVAR_90 (P x) x)))))))))));
