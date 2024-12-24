require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5056432 [A B] : Prf (∀ (λ f : El (fun A B), (= (∀ (λ k : El (fun A bool), (∃ (λ t : El (fun B bool), (= ((@GSPEC A) (λ GEN_PVAR_225 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_225 ((@IN B) (f x) t) x))))) k))))) (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (= (f x) (f y)) (= x y)))))))));
