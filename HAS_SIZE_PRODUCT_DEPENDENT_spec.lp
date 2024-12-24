require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4318348 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ m : El num, (∀ (λ t : El (fun A (fun B bool)), (∀ (λ n : El num, (⇒ (∧ ((@HAS_SIZE A) s m) (∀ (λ x : El A, (⇒ ((@IN A) x s) ((@HAS_SIZE B) (t x) n))))) ((@HAS_SIZE (prod A B)) ((@GSPEC (prod A B)) (λ GEN_PVAR_121 : El (prod A B), (∃ (λ x : El A, (∃ (λ y : El B, ((@SETSPEC (prod A B)) GEN_PVAR_121 (∧ ((@IN A) x s) ((@IN B) y (t x))) ((@̦‚ A B) x y)))))))) (* m n)))))))))));
