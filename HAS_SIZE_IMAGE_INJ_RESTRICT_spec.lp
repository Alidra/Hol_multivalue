require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4979609 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (∀ (λ P : El (fun B bool), (∀ (λ n : El num, (⇒ (∧ ((@FINITE A) s) (∧ ((@FINITE B) t) (∧ (= ((@CARD A) s) ((@CARD B) t)) (∧ ((@SUBSET B) ((@IMAGE A B) f s) t) (∧ (∀ (λ x : El A, (∀ (λ y : El A, (⇒ (∧ ((@IN A) x s) (∧ ((@IN A) y s) (= (f x) (f y)))) (= x y)))))) ((@HAS_SIZE A) ((@GSPEC A) (λ GEN_PVAR_217 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_217 (∧ ((@IN A) x s) (P (f x))) x))))) n)))))) ((@HAS_SIZE B) ((@GSPEC B) (λ GEN_PVAR_218 : El B, (∃ (λ x : El B, ((@SETSPEC B) GEN_PVAR_218 (∧ ((@IN B) x t) (P x)) x))))) n))))))))))));
