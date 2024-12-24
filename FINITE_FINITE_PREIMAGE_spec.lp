require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3617834 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ t : El (fun B bool), (⇒ (∧ ((@FINITE B) t) (∀ (λ y : El B, (⇒ ((@IN B) y t) ((@FINITE A) ((@GSPEC A) (λ GEN_PVAR_100 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_100 (= (f x) y) x)))))))))) ((@FINITE A) ((@GSPEC A) (λ GEN_PVAR_101 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_101 ((@IN B) (f x) t) x)))))))))));
