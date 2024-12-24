require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3619179 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ A' : El (fun B bool), (⇒ (∧ (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (= (f x) (f y)) (= x y)))))) ((@FINITE B) A')) ((@FINITE A) ((@GSPEC A) (λ GEN_PVAR_102 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_102 ((@IN B) (f x) A') x)))))))))));
