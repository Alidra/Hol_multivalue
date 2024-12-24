require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4323391 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (⇒ (∧ ((@FINITE A) s) ((@FINITE B) t)) ((@FINITE (prod A B)) ((@GSPEC (prod A B)) (λ GEN_PVAR_127 : El (prod A B), (∃ (λ x : El A, (∃ (λ y : El B, ((@SETSPEC (prod A B)) GEN_PVAR_127 (∧ ((@IN A) x s) ((@IN B) y t)) ((@̦‚ A B) x y))))))))))))));
