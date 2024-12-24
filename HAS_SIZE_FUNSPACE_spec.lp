require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4521678 [A B] : Prf (∀ (λ d : El B, (∀ (λ n : El num, (∀ (λ t : El (fun B bool), (∀ (λ m : El num, (∀ (λ s : El (fun A bool), (⇒ (∧ ((@HAS_SIZE A) s m) ((@HAS_SIZE B) t n)) ((@HAS_SIZE (fun A B)) ((@GSPEC (fun A B)) (λ GEN_PVAR_148 : El (fun A B), (∃ (λ f : El (fun A B), ((@SETSPEC (fun A B)) GEN_PVAR_148 (∧ (∀ (λ x : El A, (⇒ ((@IN A) x s) ((@IN B) (f x) t)))) (∀ (λ x : El A, (⇒ (¬ ((@IN A) x s)) (= (f x) d))))) f))))) (EXP n m)))))))))))));
