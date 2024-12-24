require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3616275 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ A' : El (fun B bool), (∀ (λ s : El (fun A bool), (⇒ (∧ (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x s) (∧ ((@IN A) y s) (= (f x) (f y)))) (= x y)))))) ((@FINITE B) A')) ((@FINITE A) ((@GSPEC A) (λ GEN_PVAR_95 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_95 (∧ ((@IN A) x s) ((@IN B) (f x) A')) x)))))))))))));
