require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4324156 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ m : El num, (∀ (λ t : El (fun B bool), (∀ (λ n : El num, (⇒ (∧ ((@HAS_SIZE A) s m) ((@HAS_SIZE B) t n)) ((@HAS_SIZE (prod A B)) ((@GSPEC (prod A B)) (λ GEN_PVAR_129 : El (prod A B), (∃ (λ x : El A, (∃ (λ y : El B, ((@SETSPEC (prod A B)) GEN_PVAR_129 (∧ ((@IN A) x s) ((@IN B) y t)) ((@̦‚ A B) x y)))))))) (* m n)))))))))));
