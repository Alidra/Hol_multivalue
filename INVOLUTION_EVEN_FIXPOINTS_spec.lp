require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4292765 [A] : Prf (∀ (λ f : El (fun A A), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∀ (λ x : El A, (⇒ ((@IN A) x s) (∧ ((@IN A) (f x) s) (= (f (f x)) x)))))) (= (EVEN ((@CARD A) ((@GSPEC A) (λ GEN_PVAR_118 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_118 (∧ ((@IN A) x s) (= (f x) x)) x))))))) (EVEN ((@CARD A) s))))))));
